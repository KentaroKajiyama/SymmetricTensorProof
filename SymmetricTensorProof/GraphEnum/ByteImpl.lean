import Mathlib
import SymmetricTensorProof.GraphEnum.Impl
import SymmetricTensorProof.GraphEnum.NautyFFI

namespace GraphEnumeration
namespace ByteImpl

/-
  High-performance Adjacency Matrix using a flat ByteArray.
  data[i * n + j] is 1 if edge (i, j) exists, 0 otherwise.

  This structure is optimized for execution speed:
  1. Flat memory layout (better cache locality).
  2. Uses UInt8 (0 or 1) instead of boxed Bools.
-/
structure AdjMat (n : Nat) where
  data : ByteArray
  h_size : data.size = n * n

namespace AdjMat

/- Helper for index calculation: row * n + col -/
@[inline]
def idx {n} (_g : AdjMat n) (u v : Fin n) : Nat :=
  u.val * n + v.val

/-
  ByteArray に 0 を count 回 push する関数。
  末尾再帰 (tail-recursive) なので、実行時は効率的なループにコンパイルされます。
-/
def fillZero (ba : ByteArray) (count : Nat) : ByteArray :=
  match count with
  | 0 => ba
  | c + 1 => fillZero (ba.push 0) c

/- 補題: fillZero を呼ぶとサイズが count 分増える -/
@[simp]
theorem size_fillZero (ba : ByteArray) (count : Nat) :
  (fillZero ba count).size = ba.size + count := by
  induction count generalizing ba
  case zero =>
    simp [fillZero]
  case succ c ih =>
    -- fillZero (ba.push 0) c のサイズは (ba.push 0).size + c
    simp [fillZero, ih, ByteArray.size_push]
    -- Nat の加法交換則などを解決
    omega

/- fillZero を使った初期化 -/
def empty (n : Nat) : AdjMat n :=
  let size := n * n
  let data := fillZero (ByteArray.emptyWithCapacity size) size
  { data := data,
    h_size := by
      -- fillZero の性質に関する補題を適用
      simp [data, size_fillZero]
      simp [ByteArray.size, size]}

/- Get edge status. Returns true if 1, false if 0. -/
@[inline]
def get {n} (g : AdjMat n) (u v : Fin n) : Bool :=
  let i := g.idx u v
  if h : i < g.data.size then
    g.data.get i h != 0
  else
    false -- Should not happen if constructed correctly

/- Set edge status (internal). -/
@[inline]
def set {n} (g : AdjMat n) (u v : Fin n) (b : Bool) : AdjMat n :=
  let i := g.idx u v
  if h : i < g.data.size then
    let val : UInt8 := if b then 1 else 0
    -- ByteArray.set is efficient (copy-on-write optimized)
    let newData := g.data.set i val
    have : (g.data.set i val h).size = g.data.size := by
      unfold ByteArray.size
      apply Array.size_set
    { data := newData,
      h_size := by
        simp [newData, this, g.h_size]
    }
  else
    g

-- fillZero が既存のデータの値を変更せず、新しい領域を 0 で埋めることの証明は少し手間がかかるため、
-- ここでは「空からスタートした場合」に特化した証明を書きます。

theorem get_fillZero_eq_zero {n : Nat} (i : Nat) (h : i < n) :
    (fillZero ByteArray.empty n).get i (by simp; exact h) = 0 := by
  let ba := ByteArray.empty
  -- 述語 p: 「配列の中身がすべて 0 である」
  -- これは i に依存しない、配列そのものの性質です
  let p (arr : ByteArray) := ∀ j (hj : j < arr.size), arr.get j hj = 0
  -- 補題: 任意の回数 k だけ fillZero しても、p という性質は保たれる
  -- 【重要】ここで i や h は一切登場させません
  have step (k : Nat) : ∀ arr, p arr → p (fillZero arr k) := by
    induction k with
    | zero =>
      -- ベースケース: 0回追加ならそのまま
      intros arr h_arr
      simp [fillZero]
      exact h_arr
    | succ k ih =>
      -- ステップ: k+1回追加する場合
      intros arr h_arr
      simp [fillZero]
      -- 帰納法の仮定 ih を適用する。
      -- ここでのゴールは p (fillZero (arr.push 0) k)
      -- ih の型は ∀ arr, p arr → p (fillZero arr k) なので、
      -- arr を (arr.push 0) に置き換えて適用できる。
      apply ih
      -- あとは p (arr.push 0) が成り立つこと、
      -- つまり「全部0の配列に0を足しても全部0」を示せばよい
      intro j hj
      let hj' := hj
      rw [ByteArray.size_push] at hj
      -- j が既存範囲か、新規追加位置かで分岐
      if h_lt : j < arr.size then
        -- 既存範囲: 元の配列の値を参照 (h_arr より 0)
        have : ((arr.push 0).get j hj' = 0) = ((arr.push 0)[j]'hj' = 0) := by
          simp [getElem]
        simp [this, ByteArray.get_push_lt _ _ _ h_lt]
        exact h_arr j h_lt
      else
        -- 新規位置: j = arr.size なので、push された 0 を参照
        have h_eq : j = arr.size := by omega
        subst h_eq
        have : ((arr.push 0).get arr.size hj' = 0) = ((arr.push 0)[arr.size]'hj' = 0) := by
          simp [getElem]
        simp [this, ByteArray.get_push_eq]
        -- push 0 したので当然 0

  -- 初期状態 (empty) は自明に p を満たす (要素がないため)
  have h_base : p ba := by
    intro j hj
    simp [ba] at hj -- empty.size は 0 なので、j < 0 は矛盾

  -- n回 fillZero した結果も p を満たす
  have h_all_zero := step n ba h_base
  -- 最後に、特定のインデックス i について適用する
  exact h_all_zero i _

/- Add an edge between u and v (symmetric). -/
@[inline]
def add_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v true
  g1.set v u true

/-
  Calculate the degree of a vertex u.
  Optimized to loop over the specific row slice in the ByteArray.
-/
def degree_old {n} (g : AdjMat n) (u : Fin n) : Nat :=
  let start := u.val * n
  let stop := start + n
  -- Tail-recursive loop to avoid allocation
  let rec loop (i : Nat) (count : Nat) : Nat :=
    if h : i < stop then
      -- Need to prove i < data.size for array access
      if h_bound : i < g.data.size then
        let is_edge := g.data.get i h_bound != 0
        loop (i + 1) (if is_edge then count + 1 else count)
      else
        count -- Should not happen
    else
      count
  loop start 0

/-
  【部品定義】: loopRange
  0 から n-1 までループする汎用関数です。
  @[inline] が付いているため、コンパイル時には呼び出し元の関数に展開され、
  手書きのループと全く同じコードになります。
-/
@[inline]
def loopRange {α} (n : Nat) (f : Nat → α → α) (init : α) : α :=
  let rec @[specialize] go (i : Nat) (acc : α) : α :=
    if h : i < n then
      go (i + 1) (f i acc)
    else
      acc
  go 0 init

/-
  【証明用ブリッジ】
  「このループは、論理的にはリストの foldl と同じだよ」と Lean に教える定理。
  これを一度証明しておけば、以後の証明でループの中身を気にする必要がなくなります。
-/
theorem loopRange_eq_foldl {n : Nat} {α} {f : Nat → α → α} {init : α} :
    loopRange n f init = (List.range n).foldl (fun acc i => f i acc) init := by
  rw [loopRange, List.range_eq_range']
  let go := loopRange.go n f
  -- 汎化: 任意の i と acc について証明する
  have h_go (i : Nat) (acc : α) :
    go i acc = (List.range' i (n - i) 1).foldl (fun acc i => f i acc) acc := by
    -- 【重要】n - i を k と置き、h : n - i = k という等式を保持する
    generalize h : n - i = k
    induction k generalizing i acc with
    | zero =>
      unfold go
      -- [Zeroの場合] n - i = 0 なので、i >= n。つまり i < n は False。
      have : ¬ (i < n) := by
        intro h_lt
        -- もし i < n なら n - i > 0 なので矛盾
        have : n - i > 0 := Nat.zero_lt_sub_of_lt h_lt
        omega
      simp
      -- List.range' i 0 ... は空リストなので、foldl は acc を返す
      rw [loopRange.go]
      simp [this]
    | succ k ih =>
      unfold go
      -- [Succの場合] n - i = k + 1 なので、n > i (つまり i < n)
      have h_lt : i < n := Nat.lt_of_sub_eq_succ h
      -- 1. 左辺: ループの定義を展開。i < n なので if の then 節 (再帰) に入る
      rw [loopRange.go]
      simp [h_lt]
      -- 2. 右辺: List.range' i (k + 1) を i :: List.range' (i + 1) k に分解して foldl を1回進める
      rw [List.range'_succ]
      simp
      -- 3. 帰納法の仮定 (ih) を適用するための準備
      -- IH を使うには「n - (i + 1) = k」であることを示す必要がある
      have h_idx : n - (i + 1) = k := by
        omega -- または rw [Nat.sub_add_eq, h, Nat.add_sub_cancel]
      -- 4. 帰納法の仮定を適用
      exact ih (i + 1) (f i acc) h_idx
  -- 最後に i = 0 を代入して完了
  simpa using h_go 0 init

/-
  【本番】: degree
  ByteArray を loopRange で走査します。
-/
def degree {n} (g : AdjMat n) (u : Fin n) : Nat :=
  let start := u.val * n
  -- loopRange を呼び出すだけ。
  -- コンパイルされると、start, start+1, ... とインクリメントする while ループになります。
  loopRange n (fun i count =>
    let real_idx := start + i
    -- get! は実行時の境界チェックだけ行い、証明義務を発生させません。
    -- (証明時には「論理的に正しい get」と等価であることを示します)
    if g.data.get! real_idx != 0 then count + 1 else count
  ) 0

/-
  Conversion to Reference Implementation (for Correctness proofs).
-/
def toImpl {n} (g : AdjMat n) : GraphEnumeration.AdjMat n :=
  let rows := Array.ofFn (fun (i : Fin n) =>
    Array.ofFn (fun (j : Fin n) => g.get i j)
  )
  { data := rows,
    h_size := by
      constructor
      · simp [rows]
      · intro i; simp [rows] }

end AdjMat

/-
  Optimized Candidate Generation
  Avoids creating intermediate Lists. Uses Array.range and filterMap.
-/

def get_isolated {n} (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (Fin n) :=
  let candidates := Array.range n
  candidates.filterMap (fun i =>
    if h : i < n then
      let v : Fin n := ⟨i, h⟩
      -- Check conditions: degree 0, not v1, not forbidden
      if g.degree v == 0 && v != v1 && !forbidden.contains v then
        some v
      else
        none
    else
      none
  )

def get_unused {n} (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (Fin n) :=
  let candidates := Array.range n
  candidates.filterMap (fun i =>
    if h : i < n then
      let v : Fin n := ⟨i, h⟩
      let deg := g.degree v
      -- Check conditions: 1 <= degree <= 3, not connected to v1, not v1, not forbidden
      if 1 <= deg && deg <= 3 && !g.get v1 v && v != v1 && !forbidden.contains v then
        some v
      else
        none
    else
      none
  )

def generate_next_graphs {n}
  (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (AdjMat n) :=
  let isolated := get_isolated g v1 forbidden
  -- 1. まず未使用点のグラフ列を生成 (これは常に必要)
  let unused_graphs := (get_unused g v1 forbidden).map (fun v => g.add_edge v1 v)
  if h : isolated.size > 0 then
    -- Optimization: 孤立点がある場合、"先頭の1つ" だけを採用して候補に追加
    -- (残りの孤立点は対称性により同型になるのでカットして良い)
    let v := isolated[0]'h
    let iso_graph := g.add_edge v1 v
    -- 配列の先頭に追加 (Listの h :: unused と順序を合わせるため)
    #[iso_graph] ++ unused_graphs
  else
    -- 孤立点がない場合は unused_graphs のみ
    unused_graphs

def transition {n}
  (S : Array (AdjMat n)) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (AdjMat n) :=
  S.flatMap (fun g => generate_next_graphs g v1 forbidden)

-- Placeholder for Isomorphism Reduction (computationally heaviest part)
-- opaque reduce_iso {n} (S : Array (AdjMat n)) (anchors : Array (Fin n)) : Array (AdjMat n)

-- 実装を与える
def reduce_iso {n} (S : Array (AdjMat n)) (anchors : Array (Fin n)) : Array (AdjMat n) :=
  -- 【進捗ログ】 入力サイズを表示
  -- dbg_trace は純粋関数の中で副作用（表示）を行うための特別な機能です
  dbg_trace s!"  [Reduce Iso] Input: {S.size} graphs..."
  -- 1. ByteImpl.AdjMat の配列から、生データの ByteArray 配列を取り出す
  let rawGraphs : Array ByteArray := S.map (fun g => g.data)

  -- 2. C++ (Nauty) の同型除去関数を呼び出す
  --    ※ FFI関数は純粋関数として宣言されているので、IOモナドなしで呼べます
  let uniqueRawGraphs := SymmetricTensorProof.reduceIso n rawGraphs anchors

  -- 【進捗ログ】 削減後のサイズを表示
  dbg_trace s!"  [Reduce Iso] Done. -> Output: {uniqueRawGraphs.size} graphs."

  -- 3. 結果の ByteArray を再び ByteImpl.AdjMat に包み直す
  uniqueRawGraphs.map (fun rawData =>
    { data := rawData,
      h_size := by
        sorry
    }
  )

/- 所望のグラフ列挙 -/
def enumerate_Gamma_4_4
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_1 := reduce_iso (transition S0   v1 f1) all_anchors
    let S1_2 := reduce_iso (transition S1_1 v1 f1) all_anchors
    let S1_3 := reduce_iso (transition S1_2 v1 f1) all_anchors
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_1 := reduce_iso (transition S1_3 v2 f2) all_anchors
    let S2_2 := reduce_iso (transition S2_1 v2 f2) all_anchors
    let S2_3 := reduce_iso (transition S2_2 v2 f2) all_anchors
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_1 := reduce_iso (transition S2_3 v3 f3) all_anchors
    let S3_2 := reduce_iso (transition S3_1 v3 f3) all_anchors
    let S3_3 := reduce_iso (transition S3_2 v3 f3) all_anchors
    let S3_4 := reduce_iso (transition S3_3 v3 f3) all_anchors
    -- Gamma_4 steps (Add 4 edges to v4)
    let f4 := forbidden_for v4
    let S4_1 := reduce_iso (transition S3_4 v4 f4) all_anchors
    let S4_2 := reduce_iso (transition S4_1 v4 f4) all_anchors
    let S4_3 := reduce_iso (transition S4_2 v4 f4) all_anchors
    let S4_4 := reduce_iso (transition S4_3 v4 f4) all_anchors
    S4_4
  | _ => #[]

end ByteImpl
end GraphEnumeration
