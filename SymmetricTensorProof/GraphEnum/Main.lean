import SymmetricTensorProof.GraphEnum.NautyFFI
import SymmetricTensorProof.GraphEnum.ByteImpl

open SymmetricTensorProof
open GraphEnumeration
open GraphEnumeration.ByteImpl

-- 補助関数: 生データから変換 (Mainに残しておく)
def rawToImpl {n : Nat} (raw : ByteArray) : ByteImpl.AdjMat n :=
  { data := raw, h_size := by have : raw.size = n * n := sorry; exact this }

def main : IO Unit := do
  IO.println "=== Symmetric Tensor Proof Main ==="

  let n_val : Nat := 8
  let v_list : List (Fin n_val) := [0, 1, 2, 3].map (fun i => ⟨i, sorry⟩)

  -- 1. 読み込み
  let loadedRaw ← loadGraphs n_val "initial.g6"
  let S0 := loadedRaw.map rawToImpl
  IO.println s!"Initial graphs: {S0.size}"

  -- 2. 計算実行
  -- ここで dbg_trace によるログがコンソールに流れます
  IO.println "Starting enumeration..."
  let result := enumerate_Gamma_4_4 n_val v_list S0

  -- 3. 書き出し
  IO.println s!"\nFinished. Total graphs: {result.size}"
  dumpGraph6 n_val "result.g6" (result.map (·.data))
