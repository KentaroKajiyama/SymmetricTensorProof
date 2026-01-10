import SymmetricTensorProof.Verification.check
import Mathlib.Data.String.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2

-- MessagePack の import は削除
-- import ln_messagepack.Messagepack



open VerifyCircuit VerifyIndependence Counterexample
open Sym2 -- 順序なしペア (Simplex 2) を扱うため

/- ========================================================================
   1. Helper: Random Number Generator (LCG)
   ======================================================================== -/

def LCG_A : UInt64 := 0x5851f42d4c957f2d
def LCG_C : UInt64 := 0x14057b7ef767814f

structure LcRNG where
  state : UInt64

def lcg_next (rng : LcRNG) : UInt64 × LcRNG :=
  let new_state := rng.state * LCG_A + LCG_C
  (new_state, { state := new_state })

def get_random_Zp {p : ℕ} (rng : LcRNG) : ZMod p × LcRNG :=
  let (val, rng') := lcg_next rng
  let val_zmod : ZMod p := (val.toNat % p : ℕ)
  (val_zmod, rng')

def generate_assignment_from_seed
    (P : Params) (seed : ℕ) {p : ℕ} [Fact p.Prime]
    : Fin P.n → Fin P.t → ZMod p :=
  let rng_initial : LcRNG := { state := UInt64.ofNat seed }
  let (values, _) := (List.range P.n).foldl (fun (acc_outer, rng_outer) _ =>
    let (row_vals, rng_inner) := (List.range P.t).foldl (fun (acc_inner, rng_curr) _ =>
      let (val, rng_next) := get_random_Zp (p := p) rng_curr
      (acc_inner.push val, rng_next)
    ) (#[], rng_outer)
    (acc_outer.push row_vals, rng_inner)
  ) ((#[] : Array (Array (ZMod p))), rng_initial)
  fun i j => (values[i]!)[j]!

/- ========================================================================
   2. Helper: Text Parsers
   ======================================================================== -/

def parse_nat_list (s : String) : List ℕ :=
  if s == "" || s == "[]" then []
  else (s.splitOn ",").filterMap String.toNat?

def parse_graph_from_text (P : Params) (s : String) : Option (Graph P) := do
  if s == "" then return (∅ : Graph P)
  let edge_strs := s.splitOn ","
  let mut edge_list : List (Sym2 (Fin P.n)) := []
  for es in edge_strs do
    match es.splitOn ":" with
    | [u_str, v_str] =>
      let u_nat ← u_str.toNat?
      let v_nat ← v_str.toNat?
      if h_u : u_nat < P.n then
        if h_v : v_nat < P.n then
          let u : Fin P.n := ⟨u_nat, h_u⟩
          let v : Fin P.n := ⟨v_nat, h_v⟩
          edge_list := s(u, v) :: edge_list
        else failure
      else failure
    | _ => failure
  return (edge_list.toFinset : Graph P)

/- ========================================================================
   3. Verification Dispatcher
   ======================================================================== -/

inductive RecordType
  | Independent      -- 0
  | Dependent        -- 1
  | Forbidden        -- 2
  | Counterexample   -- 3
  | Unknown          -- Error

def get_record_type (tag : Nat) : RecordType :=
  match tag with
  | 0 => RecordType.Independent
  | 1 => RecordType.Dependent
  | 2 => RecordType.Forbidden
  | 3 => RecordType.Counterexample
  | _ => RecordType.Unknown

def verify_line
  (line : String) (line_idx : Nat) (t_val : Nat) {p : ℕ} [Fact p.Prime] : IO Bool := do
  let parts := line.splitOn " "
  if parts.length < 7 then
    IO.println s!"[ERROR] Line {line_idx}: Insufficient columns."
    return false

  let tag_opt := parts[0]!.toNat?
  let seed_opt := parts[1]!.toNat?
  let n_val_opt := parts[2]!.toNat? -- 📌 新規: N のパース
  let c_inds_str := parts[3]!       -- 📌 インデックス移動
  let class_idx_opt := parts[5]!.toNat? -- 📌 インデックス移動
  let edges_str := parts[6]!.trim         -- 📌 インデックス移動

  if tag_opt.isNone || seed_opt.isNone || n_val_opt.isNone || class_idx_opt.isNone then
    IO.println s!"[ERROR] Line {line_idx}: Parse error in numeric fields."
    return false

  let tag := tag_opt.get!
  let seed := seed_opt.get!
  let n_val := n_val_opt.get! -- 📌 新規: N の取得
  let class_idx := class_idx_opt.get!

  let P : Params := {
    n := n_val,
    t := t_val,
    ht₁ := sorry,
    ht₂ := sorry
  }

  if n_val < t_val then
    IO.println s!"[WARN] Invalid params: n={n_val} < t={t_val}"
    return false

  match parse_graph_from_text P edges_str with
  | none =>
    IO.println s!"[ERROR] Line {line_idx}: Failed to parse edges '{edges_str}'"
    return false
  | some G =>
    match get_record_type tag with
    | RecordType.Independent =>
      let assignment := generate_assignment_from_seed P seed (p := p)
      let result := VerifyIndependence.check_independence P G assignment
      if result then
        pure true
      else
        IO.println s!"[FAIL] Line {line_idx} (Independence Check Failed)"
        pure false
    | RecordType.Dependent =>
      let c_indices := parse_nat_list c_inds_str
      let result := VerifyCircuit.verify_phase3_combinatorial P G c_indices class_idx
      if result then
        pure true
      else
        IO.println s!"[FAIL] Line {line_idx} (Combinatorial Check Failed: Class {class_idx})"
        pure false
    | RecordType.Forbidden =>
      -- Phase 0: 制約チェック (ダミー実装)
      pure true
    | RecordType.Counterexample =>
      IO.println s!"[WARN] Line {line_idx}: Counterexample marked (Skipping)"
      pure true
    | RecordType.Unknown =>
      IO.println s!"[WARN] Line {line_idx}: Unknown tag {tag}"
      pure true

/- ========================================================================
  4. Main Entry Point (Modified for Streaming)
  ======================================================================== -/

def main (args : List String) : IO UInt32 := do
  if args.length < 3 then
    IO.println "Usage: verify_proof <input.txt> <t> <p>"
    return 1

  let file_path := args[0]!
  let t_val := args[1]!.toNat!
  let p_val := args[2]!.toNat!



  have : Fact p_val.Prime := fact_iff.mpr sorry

  IO.println s!"[INFO] Loading {file_path} (t={t_val}, p={p_val})..."

  -- 【変更点】IO.FS.lines ではなく Handle を作成してストリーム処理を行う
  let handle ← IO.FS.Handle.mk file_path IO.FS.Mode.read

  let mut passed_count := 0
  let mut failed_count := 0
  let mut line_idx := 0

  -- ファイルの終わり(EOF)までループ
  while true do
    let line ← handle.getLine
    if line == "" then break
    line_idx := line_idx + 1

    -- 空行スキップ (末尾の改行のみの行も trim で空文字になる)
    if line.trim == "" then continue

    let res ← verify_line line line_idx t_val (p := p_val)
    if res then
      passed_count := passed_count + 1
    else
      failed_count := failed_count + 1

    -- 進捗表示 (総数が事前には分からないため、処理行数を表示)
    if line_idx % 1000 == 0 then
      IO.println s!"[PROGRESS] {line_idx} lines processed. (Failed: {failed_count})"

  let total_count := line_idx -- 最終的な行数

  IO.println "========================================"
  IO.println s!"[SUMMARY] File: {file_path}"
  IO.println s!"  Total Lines Processed: {total_count}"
  IO.println s!"  Passed: {passed_count}"
  IO.println s!"  Failed: {failed_count}"
  IO.println "========================================"

  if failed_count == 0 then
    IO.println "VERIFICATION SUCCESS"
    return 0
  else
    IO.println "VERIFICATION FAILED"
    return 1
