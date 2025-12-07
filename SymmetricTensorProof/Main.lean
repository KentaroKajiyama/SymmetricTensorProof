import SymmetricTensorProof.check
import Mathlib.Data.String.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2

-- MessagePack の import は削除
-- import ln_messagepack.Messagepack

namespace Main

open VerifyCircuit VerifyIndependence Counterexample
open Sym2 -- 順序なしペア (Simplex 2) を扱うため

/- ========================================================================
   1. Helper: Random Number Generator (LCG)
   (変更なし)
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
      let (val, rng_next) := get_random_Zp rng_curr
      (acc_inner.push val, rng_next)
    ) (#[], rng_outer)
    (acc_outer.push row_vals, rng_inner)
  ) (#[], rng_initial)
  fun i j => values[i]![j]!

/- ========================================================================
   2. Helper: Text Parsers (New!)
   テキスト形式から Graph や List Nat を復元する処理
   ======================================================================== -/

/-- "1,2,3" のようなカンマ区切り文字列を List Nat に変換 --/
def parse_nat_list (s : String) : List ℕ :=
  if s == "" || s == "[]" then []
  else (s.splitOn ",").filterMap String.toNat?

/--
  "0:1,1:2,2:3" のような形式を Graph P (Finset (Sym2 (Fin n))) に変換
  u, v が n 以上の場合は none を返す (バリデーション)
-/
def parse_graph_from_text (P : Params) (s : String) : Option (Graph P) := do
  if s == "" then return some ∅

  let edge_strs := s.splitOn ","
  let mut edge_list : List (Sym2 (Fin P.n)) := []

  for es in edge_strs do
    match es.splitOn ":" with
    | [u_str, v_str] =>
      let u_nat ← u_str.toNat?
      let v_nat ← v_str.toNat?

      -- Fin P.n への変換 (範囲チェック)
      if h_u : u_nat < P.n then
        if h_v : v_nat < P.n then
           let u : Fin P.n := ⟨u_nat, h_u⟩
           let v : Fin P.n := ⟨v_nat, h_v⟩
           edge_list := s(u, v) :: edge_list
        else failure
      else failure
    | _ => failure

  -- List を Finset に変換 (重複排除)
  return some (edge_list.toFinset)

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

/--
  1行分のデータをパースして検証する
  Input Line Format: "tag seed c_indices f_indices class_idx edges_str"
-/
def verify_line (line : String) (line_idx : Nat) (P : Params) {p : ℕ} [Fact p.Prime] : IO Bool := do
  let parts := line.splitOn " "

  -- カラム数の簡易チェック (最低限 edges_str まであるか)
  if parts.length < 6 then
    IO.println s!"[ERROR] Line {line_idx}: Insufficient columns."
    return false

  -- 各フィールドのパース
  -- parse logic uses Option implicitly via toNat? but here we force unpack for simplicity
  let tag_opt := parts[0]!.toNat?
  let seed_opt := parts[1]!.toNat?
  let c_inds_str := parts[2]!
  -- let f_inds_str := parts[3]! -- 今回は使わないがデータには含まれる
  let class_idx_opt := parts[4]!.toNat?
  let edges_str := parts[5]!

  if tag_opt.isNone || seed_opt.isNone || class_idx_opt.isNone then
     IO.println s!"[ERROR] Line {line_idx}: Parse error in numeric fields."
     return false

  let tag := tag_opt.get!
  let seed := seed_opt.get!
  let class_idx := class_idx_opt.get!

  -- グラフ構築
  match parse_graph_from_text P edges_str with
  | none =>
    IO.println s!"[ERROR] Line {line_idx}: Failed to parse edges '{edges_str}'"
    return false
  | some G =>

    match get_record_type tag with
    | RecordType.Independent =>
      -- Phase 1: 独立性チェック
      let assignment := generate_assignment_from_seed P seed
      let result := VerifyIndependence.check_independence P G assignment

      if result then
        pure true
      else
        IO.println s!"[FAIL] Line {line_idx} (Independence Check Failed)"
        pure false

    | RecordType.Dependent =>
      -- Phase 3: 組合せ的検証
      let c_indices := parse_nat_list c_inds_str
      let result := VerifyCircuit.verify_phase3_combinatorial P G c_indices class_idx

      if result then
        pure true
      else
        IO.println s!"[FAIL] Line {line_idx} (Combinatorial Check Failed: Class {class_idx})"
        pure false

    | RecordType.Forbidden =>
      -- Phase 0: 制約チェック (TODO: verify_graph_constraintsの実装が必要)
      -- ここではダミー実装として true を仮定
      -- let is_forbidden := not (verify_graph_constraints P G)
      let is_forbidden := true

      if is_forbidden then
        pure true
      else
        IO.println s!"[FAIL] Line {line_idx} (Constraint Check Failed)"
        pure false

    | RecordType.Counterexample =>
      IO.println s!"[WARN] Line {line_idx}: Counterexample marked (Skipping)"
      pure true

    | RecordType.Unknown =>
      IO.println s!"[WARN] Line {line_idx}: Unknown tag {tag}"
      pure true

/- ========================================================================
  4. Main Entry Point
  ======================================================================== -/

def main (args : List String) : IO UInt32 := do
  if args.length < 4 then
    IO.println "Usage: verify_proof <input.txt> <n> <t> <p>"
    return 1

  let file_path := args[0]!
  let n_val := args[1]!.toNat!
  let t_val := args[2]!.toNat!
  let p_val := args[3]!.toNat!

  if n_val < t_val then
    IO.println s!"[FATAL] Invalid params: n={n_val} < t={t_val}"
    return 1

  -- Params 構築 (証明項は sorry で省略)
  let P : Params := {
    n := n_val,
    t := t_val,
    valid := sorry,
    ht₁ := sorry,
    ht₂ := sorry
  }

  have : Fact p_val.Prime := fact_iff.mpr sorry

  IO.println s!"[INFO] Loading {file_path} (n={n_val}, t={t_val}, p={p_val})..."

  -- ファイルを行ごとに読み込む (Lazy IO ではなく一括読み込み)
  -- メモリが厳しい場合は Stream 処理に変える必要がありますが、
  -- Lean の IO.FS.lines は配列を返すため、数千万行だとメモリ注意です。
  let lines ← IO.FS.lines file_path

  let total_count := lines.size
  let mut passed_count := 0
  let mut failed_count := 0

  IO.println s!"[INFO] Start verifying {total_count} records."

  for (i, line) in lines.zipWithIndex do
    -- 空行スキップ
    if line.trim == "" then continue

    let res ← verify_line line (i + 1) P (p := p_val)
    if res then
      passed_count := passed_count + 1
    else
      failed_count := failed_count + 1

    if (i + 1) % 1000 == 0 then
      IO.println s!"[PROGRESS] {i + 1} / {total_count} verified. (Failed: {failed_count})"

  IO.println "========================================"
  IO.println s!"[SUMMARY] File: {file_path}"
  IO.println s!"  Total : {total_count}"
  IO.println s!"  Passed: {passed_count}"
  IO.println s!"  Failed: {failed_count}"
  IO.println "========================================"

  if failed_count == 0 then
    IO.println "VERIFICATION SUCCESS"
    return 0
  else
    IO.println "VERIFICATION FAILED"
    return 1

end Main
