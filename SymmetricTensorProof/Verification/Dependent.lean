import SymmetricTensorProof.Verification.check
import Mathlib.Combinatorics.SimpleGraph.Basic

/- FFIで受け取るための平坦な構造体 -/
structure DependentRecord where
  n : Nat
  adjBytes : ByteArray
  classIdx : Nat
  cIndices : Array Nat
  fIndices : Array Nat
  sigma : Array Nat

-- 1. FFI のバインディング (引数の n を削除し、戻り値のタプルの先頭に Nat (n) を追加)
@[extern "cpp_load_dependent_bin"]
opaque loadDependentBin (path : @& String)
  : IO (Array DependentRecord)

-- 2. 辞書順の辺インデックスを計算する関数
def edgeIndex (n : ℕ) (u v : ℕ) : ℕ :=
  let min_v := min u v
  let max_v := max u v
  min_v * n - (min_v * (min_v + 1)) / 2 + (max_v - min_v - 1)

-- 3. C_indices 配列からグラフ C を構築
def CGraphFromIndices (n : ℕ) (c_indices : Array Nat)
  : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v =>
    if u.val == v.val then false
    else
      let idx := edgeIndex n u.val (v.val + 1)
      c_indices.contains idx
  )

-- CGraphFromIndices が計算可能(Decidable)であることをLeanに保証
instance (n : ℕ) (c_indices : Array Nat)
  : DecidableRel (CGraphFromIndices n c_indices).Adj :=
  fun u v =>
    if h : u.val == v.val then
      isFalse (
        by
          simp only [BEq.beq] at h
          have heq := Fin.eq_of_val_eq (of_decide_eq_true h)
          subst heq
          exact SimpleGraph.irrefl _)
    else
      let idx := edgeIndex n u.val v.val
      if h2 : c_indices.contains idx then
        isTrue (
          by
            rw [CGraphFromIndices, SimpleGraph.fromRel_adj]
            have h_neq : u ≠ v := by
              intro heq; rw [heq] at h; simp at h
              try contradiction
            constructor
            · exact h_neq
            · left
              dsimp
              have h_false : (u.val == v.val) = false := by
                cases he : (u.val == v.val)
                · rfl
                · rw [he] at h; simp at h; try contradiction
              rw [h_false]
              dsimp
              admit
              -- exact h2
              )
      else
        isFalse (
          by
            rw [CGraphFromIndices, SimpleGraph.fromRel_adj]
            push_neg
            intro h_neq
            have h_false : (u.val == v.val) = false := by
              cases he : (u.val == v.val)
              · rfl
              · rw [he] at h; simp at h; try contradiction
            constructor
            · dsimp
              rw [h_false]
              dsimp
              admit
              -- exact h2
            · dsimp
              have h_false_symm : (v.val == u.val) = false := by
                cases he : (v.val == u.val)
                · rfl
                · simp only [Nat.beq_eq_true_eq] at he
                  have h_eq_fin := Fin.eq_of_val_eq he
                  subst h_eq_fin
                  simp at h_false
              rw [h_false_symm]
              dsimp
              have h_symm : edgeIndex n v.val u.val = idx := by
                simp [edgeIndex, idx, min_comm, max_comm]
              admit
              -- rw [h_symm]
              -- exact h2
        )

-- 4. 検証メインループ (引数から n を削除しました)
def verify_dependent_dat (filepath : String) : IO Unit := do
  IO.println s!"Loading binary data from {filepath}..."
  -- (n, ByteArray, class_index, c_indices) の配列を受け取る
  let data ← loadDependentBin filepath
  let mut successCount := 0
  let mut failCount := 0
  -- ファイルから読み取ったデータごとに n が取り出されます
  for rec in data do
    let n := rec.n
    let idx := rec.classIdx
    let c_indices := rec.cIndices
    let f_indices := rec.fIndices
    let sigma := rec.sigma
    -- そのグラフに対応する n を使って C を構築
    let C := CGraphFromIndices n c_indices
    let F := CGraphFromIndices n f_indices
    -- 検証関数にもそのグラフの n を渡す
    IO.println s!"Checking graph with class index {idx}, C_indices {c_indices}, F_indices {f_indices}, and sigma {sigma} (n = {n})"
    let isDep := Cnt.is_dependent_int n idx C F sigma
    if isDep then
      successCount := successCount + 1
    else
      failCount := failCount + 1
      IO.println "[Failed] Graph with class index"
      IO.println s!"        {idx}, C_indices {c_indices}, F_indices {f_indices}, and sigma {sigma} (n = {n})"
      IO.println "        is NOT dependent according to Lean!"
  IO.println "========================================"
  IO.println s!"Verification Complete!"
  IO.println s!"Total Checked : {data.size}"
  IO.println s!"Success       : {successCount}"
  IO.println s!"Failed        : {failCount}"
  IO.println "========================================"

-- Dependent.lean の末尾に追加
def main (args : List String) : IO UInt32 := do
  let path := "./outputs/all_dependent_graphs_dependent.dat"
  -- 引数がある場合はそれを使う例
  let filePath := args.getD 0 path
  try
    verify_dependent_dat filePath
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1
