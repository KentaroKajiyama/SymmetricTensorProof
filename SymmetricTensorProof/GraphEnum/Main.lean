import SymmetricTensorProof.GraphEnum.NautyFFI
import SymmetricTensorProof.GraphEnum.ByteImpl

open SymmetricTensorProof
open GraphEnumeration
open GraphEnumeration.ByteImpl

-- 補助関数: 生データから変換 (Mainに残しておく)
def rawToImpl {n : Nat} (raw : ByteArray) : ByteImpl.AdjMat n :=
  { data := raw, h_size := by have : raw.size = n * n := sorry; exact this }

def main (args : List String) : IO Unit := do
  IO.println "=== Symmetric Tensor Proof Main ==="

  -- 引数のチェック
  if args.length < 4 then
    IO.println "Error: Insufficient arguments."
    IO.println "Usage: lake exe main <input_file.g6> <mode: 4, 5, 6>"
    return

  let inputFile := args[0]!
  let mode := args[1]!
  let intermediatePrefix := args[2]!
  let outputPrefix := args[3]!

  -- 定数設定 (必要ならここも引数化できますが、一旦30固定とします)
  let n_val : Nat := 30
  -- アンカー (0, 1, 2, 3)
  let v_list : List (Fin n_val) := [0, 1, 2, 3].map (fun i => ⟨i, sorry⟩)

  -- 1. 読み込み
  IO.println s!"Loading graphs from: {inputFile}..."
  -- ファイルが存在しないとここでエラーになります
  let loadedRaw ← loadGraphs n_val inputFile
  let S0 := loadedRaw.map rawToImpl
  IO.println s!"Initial graphs loaded: {S0.size}"

  IO.println s!"Starting enumeration (Mode: {mode})..."

  -- 2. モード分岐
  match mode with
  | "4" =>
    main_pipeline_4 n_val v_list S0 intermediatePrefix outputPrefix
  | "5" =>
    -- main_pipeline_5 が定義されていると仮定
    IO.println "Running Pipeline 5 (Ensure main_pipeline_5 is defined)"
    main_pipeline_5 n_val v_list S0 intermediatePrefix outputPrefix
  | "6" =>
    -- main_pipeline_6 が定義されていると仮定
    IO.println "Running Pipeline 6 (Ensure main_pipeline_6 is defined)"
    main_pipeline_6 n_val v_list S0 intermediatePrefix outputPrefix
  | "support" =>
    IO.println "Running Support Pipeline (Ensure support_pipeline is defined)"
    if args.length < 5 then
      IO.println "Error: Insufficient arguments for support mode."
      IO.println
        "Usage: lake exe main <input_file.g6> support <intermediate_prefix> <output_prefix> <start_index>"
      return
    let start_index := args[4]!.toNat!
    support_pipeline n_val v_list S0 intermediatePrefix outputPrefix start_index
  | "single" =>
    IO.println "Running Single Chunk Mode"
    if args.length < 5 then
      IO.println "Error: Insufficient arguments for single mode."
      IO.println
        "Usage: lake exe main <input_file.g6> single <intermediate_prefix> <output_prefix> <chunk_index>"
      return
    let start_index := args[4]!.toNat!
    runSingleChunk n_val v_list intermediatePrefix outputPrefix start_index
  | _ =>
    IO.println s!"Error: Unknown mode '{mode}'. Please specify 4, 5, or 6."
