import Mathlib
import SymmetricTensorProof.GraphEnum.Impl

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
private def idx {n} (_g : AdjMat n) (u v : Fin n) : Nat :=
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

/- Add an edge between u and v (symmetric). -/
@[inline]
def add_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v true
  g1.set v u true

/-
  Calculate the degree of a vertex u.
  Optimized to loop over the specific row slice in the ByteArray.
-/
def degree {n} (g : AdjMat n) (u : Fin n) : Nat :=
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
  if h : isolated.size > 0 then
    -- Optimization: If isolated vertices exist, pick ONLY the first one.
    let v := isolated[0]'h
    #[g.add_edge v1 v]
  else
    -- Otherwise, try all unused vertices.
    let unused := get_unused g v1 forbidden
    unused.map (fun v => g.add_edge v1 v)

def transition {n}
  (S : Array (AdjMat n)) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (AdjMat n) :=
  S.foldl (fun acc g =>
    let nexts := generate_next_graphs g v1 forbidden
    acc ++ nexts
  ) #[]

-- Placeholder for Isomorphism Reduction (computationally heaviest part)
opaque reduce_iso {n} (S : Array (AdjMat n)) (anchors : Array (Fin n)) : Array (AdjMat n)

def enumerate_Gamma_4_4 (n : Nat) (v_list : List (Fin n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let S0 := #[AdjMat.empty n]
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
