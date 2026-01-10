import SymmetricTensorProof.GraphEnum.ByteImpl

open GraphEnumeration.ByteImpl

/-- テスト用のヘルパー: エッジリストから AdjMat を作成 -/
def mkGraph (n : Nat) (edges : List (Nat × Nat)) : AdjMat n :=
  let g0 := AdjMat.empty n
  edges.foldl (fun g (u, v) =>
    -- Fin 型への変換 (範囲外なら panic する簡易実装)
    if h : u < n ∧ v < n then
      g.add_edge ⟨u, h.1⟩ ⟨v, h.2⟩
    else
      g -- 無視
  ) g0

/-- アサーション用ヘルパー -/
def assertEq (msg : String) (actual expected : Nat) : IO Unit := do
  if actual == expected then
    IO.println s!"[PASS] {msg}"
  else
    IO.println s!"[FAIL] {msg}: Expected {expected}, got {actual}"
    throw (IO.userError "Test failed")

def main : IO Unit := do
  IO.println "=== Starting Unit Tests for C++ FFI ==="
  -- 【テスト1】: 完全な同型グラフ (N=3)
  -- 0-1, 1-2 (パスグラフ)
  let g1 := mkGraph 3 [(0, 1), (1, 2)]
  -- 0-2, 2-1 (頂点番号を付け替えただけのパスグラフ)
  let g2 := mkGraph 3 [(0, 2), (2, 1)]
  let S_case1 := #[g1, g2]
  let anchors_empty : Array (Fin 3) := #[]
  -- アンカーなしなら同型なので、1つになるはず
  let res1 := reduce_iso S_case1 anchors_empty
  assertEq "Simple Isomorphism (should merge)" res1.size 1
  -- 【テスト2】: 非同型グラフ (N=3)
  -- 0-1 (エッジ1本)
  let g3 := mkGraph 3 [(0, 1)]
  -- 0-1, 1-2 (エッジ2本)
  let g4 := mkGraph 3 [(0, 1), (1, 2)]
  let res2 := reduce_iso #[g3, g4] anchors_empty
  assertEq "Non-isomorphism (should keep both)" res2.size 2
  -- 【テスト3】: アンカー付き同型 (Anchored Isomorphism) ★重要
  -- グラフ形状: 0 - 1 - 2
  -- アンカー: [1] (真ん中の頂点を固定)
  let g_A := mkGraph 3 [(0, 1), (1, 2)] -- 1が中心
  let g_B := mkGraph 3 [(2, 1), (1, 0)] -- 1が中心 (Aと同型)

  -- グラフ形状: 1 - 0 - 2
  -- アンカー: [1] (端の頂点を固定)
  -- 形状としてはパスグラフで同じだが、アンカー「1」の位置が「端」なので
  -- アンカー固定同型の意味では g_A とは別物になるはず！
  let g_C := mkGraph 3 [(1, 0), (0, 2)]
  let anchors_1 : Array (Fin 3) := #[⟨1, by simp⟩]
  let res3 := reduce_iso #[g_A, g_B, g_C] anchors_1
  -- g_A と g_B はマージされ、g_C は残る -> 合計 2個になるはず
  assertEq "Anchored Isomorphism (should distinguish center vs leaf)" res3.size 2
  IO.println "=== All Tests Passed! ==="
