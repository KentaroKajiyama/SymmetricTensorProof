import SymmetricTensorProof.GraphEnum.NautyFFI
import SymmetricTensorProof.GraphEnum.ByteImpl

open SymmetricTensorProof
open GraphEnumeration
open GraphEnumeration.ByteImpl

--------------------------------------------------------------------------------
-- ヘルパー関数
--------------------------------------------------------------------------------

/-- グラフの辺の数を数える (無向グラフを想定して /2 する) -/
def countEdges (n : Nat) (mat : SymmetricTensorProof.AdjMat) : Nat :=
  let size := mat.size
  -- 安全のためサイズチェック
  if size != n * n then
    0 -- エラー値
  else
    let rec loop (i : Nat) (cnt : Nat) : Nat :=
      if i >= size then cnt
      else
        -- バイトが 0 より大きければ辺があるとみなす
        let val := if mat.get! i > 0 then 1 else 0
        loop (i + 1) (cnt + val)
    (loop 0 0) / 2

/-- 配列の要素を複製してテストデータを作る -/
def duplicateArray {α} (arr : Array α) (times : Nat) : Array α :=
  let rec loop (i : Nat) (acc : Array α) : Array α :=
    match i with
    | 0 => acc
    | n + 1 => loop n (acc ++ arr)
  loop times #[]

--------------------------------------------------------------------------------
-- テスト本体
--------------------------------------------------------------------------------

def main : IO Unit := do
  IO.println "=== Start Nauty Unit Test ==="

  -- 【設定】
  -- 辺数 15~21 を想定する場合、n=8 あれば完全グラフ(28辺)まで入るので十分です
  let n : Nat := 8

  -- テスト用ファイル (事前に用意してください)
  -- 例: n=8, edges=15 程度のグラフが含まれるファイル
  let inputFile := "test.g6"
  let outputFile := "output_test.g6"

  IO.println s!"Target N: {n}"
  IO.println s!"Input File: {inputFile}"

  -- ---------------------------------------------------------
  -- Test 1: Load (読み込みテスト)
  -- ---------------------------------------------------------
  IO.println "\n[Test 1] Loading graphs..."

  -- エラーハンドリング: ファイルがない場合に落ちないように try-catch は
  -- IOモナドの標準機能では簡易的なので、ここでは存在確認してからロードします
  if ← System.FilePath.pathExists inputFile then
    let loadedGraphs ← loadGraphs n inputFile
    IO.println s!"  -> Success. Loaded {loadedGraphs.size} graphs."

    if loadedGraphs.size == 0 then
      IO.println "  -> WARNING: File is empty. Creating dummy data for further tests."
      -- データがないとテストできないので、ダミー（空グラフ）を作る
      let dummy := ByteArray.mk (Array.mkEmpty (n * n))
      let loadedGraphs := #[dummy]
      pure ()
    else
      -- 最初のグラフの情報を表示
      let g0 := loadedGraphs[0]!
      let edges := countEdges n g0
      IO.println s!"  -> First graph edges: {edges}"
      IO.println s!"  -> Raw byte size: {g0.size} (Expected: {n*n})"

      if g0.size != n * n then
        IO.println "  -> FATAL: Graph size mismatch! Check C++ glue code."
        return

      -- ---------------------------------------------------------
      -- Test 2: Reduce Iso Logic (同型除去のロジックテスト)
      -- ---------------------------------------------------------
      IO.println "\n[Test 2] Testing Isomorphism Reduction (Deduplication)..."

      -- 【検証方法】
      -- 読み込んだグラフの「最初の1個」を取り出し、それを「3回複製」した配列を作ります。
      -- これを reduceIso にかけた結果、サイズが「1」に戻れば、Nauty は正しく動作しています。

      let targetGraph := loadedGraphs[0]!
      let duplicatedBatch := #[targetGraph, targetGraph, targetGraph]

      IO.println s!"  -> Created a batch of {duplicatedBatch.size} identical graphs."

      -- アンカーなし (#[] ) で実行
      let reducedBatch := reduceIso n duplicatedBatch #[]

      IO.println s!"  -> After reduceIso: {reducedBatch.size} graphs."

      if reducedBatch.size == 1 then
        IO.println "  -> PASS: Deduplication worked correctly."
      else
        IO.println s!"  -> FAIL: Expected 1 graph, but got {reducedBatch.size}."

      -- ---------------------------------------------------------
      -- Test 3: Anchors (アンカー指定テスト)
      -- ---------------------------------------------------------
      IO.println "\n[Test 3] Testing with Anchors..."

      -- 頂点 0 を固定 (アンカー) して同型判定を行う
      -- Fin n 型を作るために証明が必要ですが、リテラルならこれでOK
      if h_n : 0 < n then
        let v0 : Fin n := ⟨0, h_n⟩
        let anchors := #[v0]

        -- アンカーを指定してもクラッシュしないか確認
        let reducedAnchored := reduceIso n duplicatedBatch anchors
        IO.println s!"  -> Ran with anchor [0]. Result size: {reducedAnchored.size}"
        IO.println "  -> PASS: Execution with anchors finished without errors."
      else
        IO.println "  -> Skip: n is 0."

      -- ---------------------------------------------------------
      -- Test 4: Dump (書き出しテスト)
      -- ---------------------------------------------------------
      IO.println "\n[Test 4] Dumping graphs to file..."

      dumpGraph6 n outputFile reducedBatch

      if ← System.FilePath.pathExists outputFile then
        IO.println s!"  -> Success. '{outputFile}' was created."
      else
        IO.println s!"  -> FAIL: '{outputFile}' was NOT created."

  else
    IO.println s!"Error: Input file '{inputFile}' not found. Please create it first."

  IO.println "\n=== Test Finished ==="
