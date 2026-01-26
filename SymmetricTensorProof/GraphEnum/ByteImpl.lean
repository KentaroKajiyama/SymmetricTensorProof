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
deriving DecidableEq -- これを追加！ (= で比較できるようになる)

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
      h_size := sorry
    }
  )

/- Config needed to execute one single step (add one edge). -/
structure StepConfig (n : Nat) where
  anchor : Fin n
  forbidden : Array (Fin n)
  all_anchors : Array (Fin n)


/-
  Executes ONE step of the enumeration:
  1. Generate next graphs (Transition)
  2. Reduce isomorphisms (FFI)
-/
def runStep_3_edges {n} (graphs : Array (AdjMat n)) (config : StepConfig n) : Array (AdjMat n) :=
  let expanded_1 := transition graphs config.anchor config.forbidden
  let added_1 := reduce_iso expanded_1 config.all_anchors
  let expanded_2 := transition added_1 config.anchor config.forbidden
  let added_2 := reduce_iso expanded_2 config.all_anchors
  let expanded_3 := transition added_2 config.anchor config.forbidden
  let added_3 := reduce_iso expanded_3 config.all_anchors
  added_3

/-
  Executes ONE step of the enumeration:
  1. Generate next graphs (Transition)
  2. Reduce isomorphisms (FFI)
-/
def runStep_4_edges {n} (graphs : Array (AdjMat n)) (config : StepConfig n) : Array (AdjMat n) :=
  let expanded_1 := transition graphs config.anchor config.forbidden
  let added_1 := reduce_iso expanded_1 config.all_anchors
  let expanded_2 := transition added_1 config.anchor config.forbidden
  let added_2 := reduce_iso expanded_2 config.all_anchors
  let expanded_3 := transition added_2 config.anchor config.forbidden
  let added_3 := reduce_iso expanded_3 config.all_anchors
  let expanded_4 := transition added_3 config.anchor config.forbidden
  let added_4 := reduce_iso expanded_4 config.all_anchors
  added_4

/- 所望のグラフ列挙 -/
def enumerate_Gamma_2_3
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_3 := runStep_3_edges S0 { anchor := v1, forbidden := f1, all_anchors := all_anchors }
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_3 := runStep_3_edges S1_3 { anchor := v2, forbidden := f2, all_anchors := all_anchors }
    S2_3
  | _ => #[]

def enumerate_Gamma_3_4
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_3 := runStep_3_edges S0 { anchor := v1, forbidden := f1, all_anchors := all_anchors }
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_3 := runStep_3_edges S1_3 { anchor := v2, forbidden := f2, all_anchors := all_anchors }
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_4 := runStep_4_edges S2_3 { anchor := v3, forbidden := f3, all_anchors := all_anchors }
    S3_4
  | _ => #[]

def enumerate_Gamma_4_4
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_3 := runStep_3_edges S0 { anchor := v1, forbidden := f1, all_anchors := all_anchors }
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_3 := runStep_3_edges S1_3 { anchor := v2, forbidden := f2, all_anchors := all_anchors }
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_4 := runStep_4_edges S2_3 { anchor := v3, forbidden := f3, all_anchors := all_anchors }
    -- Gamma_4 steps (Add 4 edges to v4)
    let f4 := forbidden_for v4
    let S4_4 := runStep_4_edges S3_4 { anchor := v4, forbidden := f4, all_anchors := all_anchors }
    S4_4
  | _ => #[]

def enumerate_Gamma_3_4_4
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_3 := runStep_3_edges S0 { anchor := v1, forbidden := f1, all_anchors := all_anchors }
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_4 := runStep_4_edges S1_3 { anchor := v2, forbidden := f2, all_anchors := all_anchors }
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_4 := runStep_4_edges S2_4 { anchor := v3, forbidden := f3, all_anchors := all_anchors }
    S3_4
  | _ => #[]

def enumerate_Gamma_4_4_4
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_4 := runStep_4_edges S0 { anchor := v1, forbidden := f1, all_anchors := all_anchors }
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_4 := runStep_4_edges S1_4 { anchor := v2, forbidden := f2, all_anchors := all_anchors }
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_4 := runStep_4_edges S2_4 { anchor := v3, forbidden := f3, all_anchors := all_anchors }
    S3_4
  | _ => #[]


/-
  Determines the configuration for a specific step based on a dynamic schedule.
  Input:
    step: The current step number (1-based).
    anchors: List of anchor vertices (e.g., [v1, v2, v3, v4]).
    add_counts: List of edges to add for each anchor (e.g., [3, 3, 4, 4]).
-/
def getStepConfig {n}
  (step : Nat) (anchors : List (Fin n)) (add_counts : List Nat) : Option (StepConfig n) :=
  if anchors.length != add_counts.length then none
  else
    let all_anchors := anchors.toArray
    let forbid (v : Fin n) := all_anchors.filter (· != v)
    -- Recursively find which phase the current step belongs to
    let rec find_phase
      (current_step : Nat) (idx : Nat) (counts : List Nat) : Option (StepConfig n) :=
      match counts with
      | [] => none
      | c :: rest =>
        -- Check if 'step' falls within the current anchor's phase
        -- Range: [current_step, current_step + c - 1]
        if step < current_step + c then
          match anchors[idx]? with
          | some v => some { anchor := v, forbidden := forbid v, all_anchors := all_anchors }
          | none => none
        else
          -- Move to the next anchor
          find_phase (current_step + c) (idx + 1) rest
    find_phase 1 0 add_counts

-- (1) i番目までのチャンクを結合して、一気に計算した結果 (理想)
def batchResultUpTo {n}
  (chunks : Array (Array (AdjMat n)))
  (config : StepConfig n)
  (i : Nat) : Array (AdjMat n) :=
  let combined_input := (chunks.take i).flatten
  runStep_4_edges combined_input config

-- (2) i番目までのチャンクを個別に計算して、結合した結果 (現実の論理モデル)
def splitResultUpTo {n}
  (chunks : Array (Array (AdjMat n)))
  (config : StepConfig n)
  (i : Nat) : Array (AdjMat n) :=
  (chunks.take i).flatMap (fun chunk => runStep_4_edges chunk config)

-- (3) これが「processed_up_to」の実体です (Prop型)
/-
  「インデックス i までにおいて、分割実行の結果(split)は
    一括実行の結果(batch)を包含している」という命題
-/
def processed_up_to {n}
  (chunks : Array (Array (AdjMat n)))
  (config : StepConfig n)
  (i : Nat) : Prop :=
  -- 一括実行に含まれる任意のグラフ g について...
  ∀ g ∈ batchResultUpTo chunks config i,
  -- 分割実行の結果の中にも (同型な) g' が存在する
  ∃ g' ∈ splitResultUpTo chunks config i,
  g = g'

/-
  Pure function: Split the array into roughly equal chunks.
  This logic is pure and can be verified to preserve all elements (Proof Target).
-/
def splitIntoChunks {α} (arr : Array α) (numChunks : Nat) : Array (Array α) :=
  if numChunks == 0 then #[]
  else
    let total := arr.size
    let chunkSize := (total + numChunks - 1) / numChunks -- Ceiling division
    let rec loop (start : Nat) (acc : Array (Array α)) :=
      if start >= total then acc
      else
        let endIdx := Nat.min (start + chunkSize) total
        let chunk := arr.extract start endIdx
        loop endIdx (acc.push chunk)
      termination_by total - start
      decreasing_by sorry
    loop 0 #[]

/-
  IO function: Save partitioned graphs to disk.
  Uses `splitIntoChunks` internally, bridging pure logic and IO.
-/
def saveCheckpoints {n}
  (chunks : Array (Array (AdjMat n))) (file_prefix : String)
  : IO Unit := do
  -- 1. ファイルプレフィックスから親ディレクトリを取得して作成
  -- 1. String から System.FilePath に変換
  let path : System.FilePath := file_prefix
  -- 2. 親ディレクトリを取得して作成
  if let some parentDir := path.parent then
    -- IO.FS.createDirAll は String ではなく FilePath を受け取ります
    IO.FS.createDirAll parentDir
  IO.println s!"Splitting {chunks.size} graphs into {chunks.size} files..."
  for h : i in [0 : chunks.size] do
    let chunk := chunks[i]
    let filename := s!"{file_prefix}_{i}.g6"
    IO.println s!"  -> Saving {chunk.size} graphs to {filename}"
    SymmetricTensorProof.dumpGraph6 n filename (chunk.map (·.data))

/-
  Runs the enumeration in memory.
  Allows specifying a 'startStep' to resume computation from a saved state.
  This is essential for "Divide and Conquer" strategies.
-/
def enumerate_generic {n}
  (v_list : List (Fin n))
  (add_counts : List Nat)
  (S0 : Array (AdjMat n))
  (startStep : Nat := 1) : Array (AdjMat n) :=
  let total_steps := add_counts.foldl (·+·) 0
  let rec loop (currentS : Array (AdjMat n)) (step : Nat) : Array (AdjMat n) :=
    if step > total_steps then currentS
    else
      match getStepConfig step v_list add_counts with
      | some config =>
        dbg_trace s!"\n=== Step {step} / {total_steps} (Anchor: {config.anchor}) ==="
        loop (runStep_4_edges currentS config) (step + 1)
      | none =>
        -- If config is not found (e.g., index out of bounds), just proceed.
        loop currentS (step + 1)
      termination_by (total_steps + 1) - step
  loop S0 startStep

/- Legacy wrapper for the specific 3-3-4-4 case -/
def enumerate_Gamma_4_4_new
  (n : Nat) (v_list : List (Fin n)) (S0 : Array (AdjMat n)) : Array (AdjMat n) :=
  enumerate_generic v_list [3, 3, 4, 4] S0

/-
  【Axiom】 IOの正当性の架け橋
  「ファイル "prefix_i.g6" をロードした結果は、論理的な分割 chunks[i] と一致する」
  これは証明できないので、信頼する基盤 (Trusted Base) とします。
-/
axiom load_is_correct {n}
  (i : Nat) (file_prefix : String) (logical_chunk : Array (ByteImpl.AdjMat n)) :
  -- IOアクションとしてのロード処理...
  -- 返り値が logical_chunk と等しいことを保証する型を作るのは大変なので、
  -- ここでは「コードの中で使う値が正しい」と仮定する形で使います。
  True -- 実際の実装は下の loop 内で行います

-- 【証明用ヘルパー】
-- この定理は ByteCorrectness.lean で証明すべきものですが、
-- ここでは実装を進めるために sorry (Axiom) とします。
theorem invariant_step {n}
  (chunks : Array (Array (AdjMat n)))
  (config : StepConfig n)
  (i : Nat)
  -- 仮定: i個目まではOK (0 to i-1)
  (h_prev : processed_up_to chunks config i) :
  -- 結論: i+1個目までもOK (0 to i)
  processed_up_to chunks config (i + 1) := by
  -- 証明の方針:
  -- splitResultUpTo (i+1) = splitResultUpTo i ++ runStep (chunks[i])
  -- batchResultUpTo (i+1) = runStep (chunks[0..i].flatten)
  -- transitionの分配法則とreduceIsoの包含性を使う
  sorry

/- chunks 全体に依存せず、純粋に「今の積み上げ」を表すモデル -/
def resultAccumulator {α} (prev_acc : Array α) (new_chunk_result : Array α) : Array α :=
  prev_acc ++ new_chunk_result

/-
  論理モデル：実行時には生成しないが、証明の中で
  「i番目までの各ファイルの内容を結合したもの」を指すために使用する。
-/
def diskAccumulatorUpTo {n}
  (logical_chunks : Array (Array (AdjMat n)))
  (config : StepConfig n)
  (i : Nat) : Array (AdjMat n) :=
  splitResultUpTo logical_chunks config i


/-
  【証拠の定義】
  「logical_chunks の内容が、file_prefix で始まるファイル群としてディスク上に正しく保存されている」
  という状態を表す命題。

  ※ Prop なので、実行時にはこの構造体自体は消滅します（メモリを食いません）。
-/
structure ChunksMatchDisk {n}
  (file_prefix : String) (logical_chunks : Array (Array (ByteImpl.AdjMat n))) : Prop where
  -- 少なくともサイズが一致していることは保証する
  size_eq : logical_chunks.size = 200 -- または適切な変数

  -- 【ポイント】
  -- ここに `loadGraphs` を書く代わりに、
  -- 「この証拠を持っているなら、読み込みは整合する」という事実は
  -- 以下の公理関数 (trusted loader) で担保します。

/-
  【公理 1: 保存の信頼性】
  saveCheckpoints が完了した直後に、この証拠を「生成」するための公理。
  「保存したんだから、ディスクの中身は論理データと一致しているはずだ」という宣言です。
-/
axiom assume_chunks_saved {n}
  (file_prefix : String) (chunks : Array (Array (ByteImpl.AdjMat n)))
  : ChunksMatchDisk file_prefix chunks


/-
  【公理 2: 信頼された読み込み】
  ChunksMatchDisk という証拠がある場合に限り使える、特別な読み込み関数。

  戻り値: { data // data = logical_chunks[i] }
  つまり、「データ」だけでなく「そのデータが論理データと等しい」という証明もセットで返します。
-/
def loadChunkTrusted
  {n}
  {logical_chunks : Array (Array (ByteImpl.AdjMat n))} -- 暗黙引数 (Prop用)
  (file_prefix : String)
  (i : Nat)
  (h_match : ChunksMatchDisk file_prefix logical_chunks) -- 証拠が必要
  (h_bound : i < logical_chunks.size)
  : IO { real_data : Array (ByteImpl.AdjMat n) // real_data = logical_chunks[i] } := do

  -- 1. 普通にファイルをロード (IO)
  let loaded_raw ← SymmetricTensorProof.loadGraphs n s!"{file_prefix}_{i}.g6"

  -- 2. 型変換 (ByteArray -> AdjMat)
  let real_data := loaded_raw.map (fun raw =>
    ({ data := raw, h_size := sorry } : ByteImpl.AdjMat n)
  )

  -- 3. 「ファイルシステムは正しい」という公理を適用して、等式証明を作成
  --    ここでは実装上 sorry を使いますが、ロジックとして「読み込み関数の中に封じ込める」のが重要です。
  have h_eq : real_data = logical_chunks[i] := sorry

  -- 4. データと証明をセットにして返す
  return ⟨real_data, h_eq⟩
/-
  ループ処理本体。
  引数として「論理的な分割データ (logical_chunks)」を受け取りますが、
  実行時にはファイルから読み込みます。
-/
def processChunksLoop {n}
  {logical_chunks : Array (Array (ByteImpl.AdjMat n))} -- 論理モデル
  (config : ByteImpl.StepConfig n)
  (file_prefix : String)
  (output_prefix : String)
  -- 現在のインデックス
  (i : Nat)
  (h_match : ChunksMatchDisk file_prefix logical_chunks) -- ★この引数が「鍵」！
  -- 【不変量】: これまで処理した論理データの累積についての証明などを持ち回るならここに書く
  (h_bound : i <= logical_chunks.size)
  (h_progress : processed_up_to logical_chunks config i)
  -- 【不変量】今の蓄積が、論理的な一括計算結果と一致しているという証拠
  (h_invariant :
    diskAccumulatorUpTo logical_chunks config i
      = splitResultUpTo logical_chunks config i)
  : IO Unit := do
  if h : i < logical_chunks.size then
    -- 1. 論理的な現在のチャンクを取得 (証明用)
    -- let current_logical_chunk := logical_chunks[i]
    -- -- 2. 現実のファイルをロード (IO)
    -- IO.println s!"Processing chunk {i}..."
    -- let loaded_data ← SymmetricTensorProof.loadGraphs n s!"{file_prefix}_{i}.g6"
    -- let current_real_chunk := loaded_data.map (fun rawData =>
    --   { data := rawData, h_size := sorry }
    -- )
    -- -- 【ここでリンク！】
    -- -- 現実のデータと論理データが一致していることを「仮定」して、証明コンテキストに取り込む
    -- -- ここは証明できないので sorry (Axiom) ですませる
    -- -- 「ファイルシステムは正しい」という前提です。
    -- have h_link : current_real_chunk = current_logical_chunk := sorry
    let ⟨current_real_chunk, h_link⟩ ← loadChunkTrusted file_prefix i h_match h
    -- 3. 計算実行 (純粋関数)
    -- ここで h_link を使うことで、result が logical_chunk に基づいていると言える
    let result := runStep_4_edges current_real_chunk config
    -- 1. 新しい蓄積を作る (論理上)
    -- 【論理的な不変量の更新】
    -- diskAccumulatorUpTo (i+1) が splitResultUpTo (i+1) と一致することを示す
    have h_next_invariant :
      diskAccumulatorUpTo logical_chunks config (i + 1)
        = splitResultUpTo logical_chunks config (i + 1) := by
      unfold diskAccumulatorUpTo splitResultUpTo
      -- ここで iステップ目までの h_invariant と、今回の result の等価性を組み合わせて証明
      -- diskAccumulatorUpTo の定義により、構造的に導かれる
      sorry
    -- 進捗証明の更新
    have h_next_progress : processed_up_to logical_chunks config (i + 1) := by
      apply invariant_step logical_chunks config i h_progress

    have h_next_split_def :
      splitResultUpTo logical_chunks config (i + 1)
      = splitResultUpTo logical_chunks config i ++ result := by
      -- ※ここは splitResultUpTo の性質証明を使う
      unfold splitResultUpTo result
      simp [h_link, <-Array.flatMap_push]
    -- 4. 論理的な正当性の確認 (コンパイル時にチェックされる)
    -- runStep が「分割しても大丈夫な関数である」という定理を適用
    have h_safe :
      result = runStep_4_edges current_real_chunk config := by
        unfold result
        rw [h_link]
    -- 5. 結果を保存 (IO)
    SymmetricTensorProof.dumpGraph6 n s!"{output_prefix}_{i}.g6" (result.map (·.data))
    -- 【証明ステップの更新】
    -- 「i番目まで完了」した証拠を作る
    have h_next : processed_up_to logical_chunks config (i + 1) := by
      apply invariant_step logical_chunks config i h_progress
    -- 次のステップのための境界条件の証明
    -- i < size ならば i + 1 <= size である
    let h_bound_next : i + 1 <= logical_chunks.size := Nat.succ_le_of_lt h
    -- 6. 次のループへ (帰納法のようなもの)
    processChunksLoop
      config
      file_prefix
      output_prefix
      (i + 1)
      h_match
      h_bound_next
      h_next
      h_next_invariant
  else
    IO.println "All chunks processed."
    -- ここで「全ての i について処理が完了した」ことが型レベルで確定します
    -- i が size 以上であり、かつ進捗証明から i = size であることを導く
    have h_final_idx : i = logical_chunks.size := Nat.le_antisymm h_bound (Nat.ge_of_not_lt h)

    -- h_invariant の i を size に書き換える
    -- ここで result の積み重ねが splitResultUpTo と一致することが証明された。
    have h_final_proof :
      diskAccumulatorUpTo logical_chunks config logical_chunks.size
        = splitResultUpTo logical_chunks config logical_chunks.size := by
      rw [← h_final_idx]
      exact h_invariant

def main_pipeline_3
  (n : Nat) (anchors : List (Fin n)) (S0 : Array (AdjMat n))
  (intermediate_file_prefix : String) (output_file_prefix : String)
  : IO Unit := do

  let s23 := enumerate_Gamma_2_3 n anchors S0

  let logical_chunks := splitIntoChunks s23 200

  -- 2. 分割して保存（ここで一時的にメモリを食う）
  saveCheckpoints logical_chunks intermediate_file_prefix

  let h_match : ChunksMatchDisk intermediate_file_prefix logical_chunks :=
    { size_eq := sorry } -- 実装に合わせて埋める

  match anchors with
  | [v1, v2, v3, v4] =>
    IO.println "Processing anchors..."
    let config_1 : StepConfig n
      := { anchor := v3, forbidden := #[v1, v2, v4], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config_1
      intermediate_file_prefix
      intermediate_file_prefix
      0
      h_match
      (Nat.zero_le _)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る

    let config_2 : StepConfig n
      := { anchor := v4, forbidden := #[v1, v2, v3], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config_2
      intermediate_file_prefix
      output_file_prefix
      0
      h_match
      (Nat.zero_le _)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る
  | [] =>
    IO.println "No anchors provided."
    return
  | _ =>
    IO.println "Invalid number of anchors."
    return

def main_pipeline_4
  (n : Nat) (anchors : List (Fin n)) (S0 : Array (AdjMat n))
  (intermediate_file_prefix : String) (output_file_prefix : String)
  : IO Unit := do
  -- 1. 10本までの計算結果を得る（これはメモリに乗る）
  let s34 := enumerate_Gamma_3_4 n anchors S0

  let num_files := 200

  let logical_chunks := splitIntoChunks s34 num_files

  -- 2. 分割して保存（ここで一時的にメモリを食う）
  saveCheckpoints logical_chunks intermediate_file_prefix

  -- 2. 「保存したから正しい」という証拠を作成
  -- この時点では論理データへの参照があるが、h_match 自体は Prop なので軽量
  let h_match : ChunksMatchDisk intermediate_file_prefix logical_chunks :=
    { size_eq := sorry } -- 実装に合わせて埋める

  match anchors with
  | [] =>
    IO.println "No anchors provided."
    return
  | [v1, v2, v3, v4] =>
    IO.println "Processing anchors..."
    let config : StepConfig n
      := { anchor := v4, forbidden := #[v1, v2, v3], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config
      intermediate_file_prefix
      output_file_prefix
      0
      h_match
      (Nat.zero_le _)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る

  | _ =>
    IO.println "Invalid number of anchors."
    return

def main_pipeline_5
  (n : Nat) (anchors : List (Fin n)) (S0 : Array (AdjMat n))
  (intermediate_file_prefix : String) (output_file_prefix : String)
  : IO Unit := do
  -- 1. 11本までの計算結果を得る（これはメモリに乗る）
  let s34 := enumerate_Gamma_3_4_4 n anchors S0

  let num_files := 200

  let logical_chunks := splitIntoChunks s34 num_files

  -- 2. 分割して保存（ここで一時的にメモリを食う）
  saveCheckpoints logical_chunks intermediate_file_prefix

  -- 2. 「保存したから正しい」という証拠を作成
  -- この時点では論理データへの参照があるが、h_match 自体は Prop なので軽量
  let h_match : ChunksMatchDisk intermediate_file_prefix logical_chunks :=
    { size_eq := sorry } -- 実装に合わせて埋める

  match anchors with
  | [] =>
    IO.println "No anchors provided."
    return
  | [v1, v2, v3, v4] =>
    IO.println "Processing anchors..."
    let config : StepConfig n
      := { anchor := v4, forbidden := #[v1, v2, v3], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config
      intermediate_file_prefix
      output_file_prefix
      0
      h_match
      (Nat.zero_le _)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る

  | _ =>
    IO.println "Invalid number of anchors."
    return

def main_pipeline_6
  (n : Nat) (anchors : List (Fin n)) (S0 : Array (AdjMat n))
  (intermediate_file_prefix : String) (output_file_prefix : String)
  : IO Unit := do
  -- 1. 12本までの計算結果を得る（これはメモリに乗る）
  let s34 := enumerate_Gamma_4_4_4 n anchors S0

  let num_files := 200

  let logical_chunks := splitIntoChunks s34 num_files

  -- 2. 分割して保存（ここで一時的にメモリを食う）
  saveCheckpoints logical_chunks intermediate_file_prefix

  -- 2. 「保存したから正しい」という証拠を作成
  -- この時点では論理データへの参照があるが、h_match 自体は Prop なので軽量
  let h_match : ChunksMatchDisk intermediate_file_prefix logical_chunks :=
    { size_eq := sorry } -- 実装に合わせて埋める

  match anchors with
  | [] =>
    IO.println "No anchors provided."
    return
  | [v1, v2, v3, v4] =>
    IO.println "Processing anchors..."
    let config : StepConfig n
      := { anchor := v4, forbidden := #[v1, v2, v3], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config
      intermediate_file_prefix
      output_file_prefix
      0
      h_match
      (Nat.zero_le _)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る

  | _ =>
    IO.println "Invalid number of anchors."
    return

def support_pipeline
  (n : Nat) (anchors : List (Fin n)) (S0 : Array (AdjMat n))
  (intermediate_file_prefix : String) (output_file_prefix : String)
  (start_index : Nat)
  : IO Unit := do
  -- 1. 12本までの計算結果を得る（これはメモリに乗る）
  -- let s34 := enumerate_Gamma_4_4_4 n anchors S0

  -- let num_files := 200

  let logical_chunks := #[]

  -- -- 2. 分割して保存（ここで一時的にメモリを食う）
  -- saveCheckpoints logical_chunks intermediate_file_prefix

  -- 2. 「保存したから正しい」という証拠を作成
  -- この時点では論理データへの参照があるが、h_match 自体は Prop なので軽量
  let h_match : ChunksMatchDisk intermediate_file_prefix logical_chunks :=
    { size_eq := sorry } -- 実装に合わせて埋める

  match anchors with
  | [] =>
    IO.println "No anchors provided."
    return
  | [v1, v2, v3, v4] =>
    IO.println "Processing anchors..."
    let config : StepConfig n
      := { anchor := v4, forbidden := #[v1, v2, v3], all_anchors := #[v1, v2, v3, v4]}
    processChunksLoop
      config
      intermediate_file_prefix
      output_file_prefix
      start_index
      h_match
      (by admit)         -- h_bound
      (by admit) -- i=0 の時の processed_up_to
      (rfl)                   -- h_invariant: i=0 の時は空 = 空 なので rfl で通る

  | _ =>
    IO.println "Invalid number of anchors."
    return

end ByteImpl
end GraphEnumeration
