import Mathlib

namespace GraphEnumeration

/-
Adjacency Matrix structure for a graph with n vertices.
data[i][j] is true if there is an edge between i and j.
We include a proof that the dimensions are exactly n x n.
-/
structure AdjMat (n : Nat) where
  data : Array (Array Bool)
  h_size : data.size = n ∧ ∀ (i : Fin data.size), (data[i]).size = n

namespace AdjMat

/- Create an empty graph with n vertices. -/
def empty (n : Nat) : AdjMat n :=
  let row := Array.replicate n false
  let data := Array.replicate n row
  { data := data,
    h_size := by
      constructor
      · rw [Array.size_replicate]
      · intro i
        change (Array.replicate n (Array.replicate n false))[i].size = n
        simp [Array.getElem_replicate, Array.size_replicate]
  }

/- Safe access to the adjacency matrix. -/
def get {n} (g : AdjMat n) (u v : Fin n) : Bool :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  let col_idx : Fin row.size := ⟨v.val, by
    have h : row.size = n := g.h_size.2 row_idx
    rw [h]; exact v.isLt⟩
  row[col_idx]

/- Private helper to set a value in the matrix. -/
def set {n} (g : AdjMat n) (u v : Fin n) (b : Bool) : AdjMat n :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  let col_idx : Fin row.size := ⟨v.val, by
    have h : row.size = n := g.h_size.2 row_idx
    rw [h]; exact v.isLt⟩
  let new_row := row.set col_idx b
  let new_data := g.data.set row_idx new_row
  { data := new_data,
    h_size := by
      constructor
      · rw [Array.size_set, g.h_size.1]
      · intro i
        dsimp
        rw [Array.getElem_set]
        split
        · rw [Array.size_set]
          convert g.h_size.2 _
        · have h_sz : (g.data.set row_idx new_row).size = g.data.size := by simp [Array.size_set]
          convert g.h_size.2 ⟨i.val, h_sz ▸ i.isLt⟩
  }

/- Add an edge between u and v (symmetric). -/
def add_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v true
  g1.set v u true

/-
  Calculate the degree of a vertex u.
  Counts the number of 'true' values in the u-th row.
-/
def degree {n} (g : AdjMat n) (u : Fin n) : Nat :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  row.foldl (fun count b => if b then count + 1 else count) 0

/- get と set をつなぐ lemma -/
lemma get_set_eq {n} (g : AdjMat n) (u v x y : Fin n) (b : Bool) :
    (g.set u v b).get x y = if x = u ∧ y = v then b else g.get x y := by
  simp [get, set]
  simp only [Array.getElem_set]
  by_cases h1 : u = x <;> by_cases h2 : v = y
  · subst h1; subst h2; simp
  · subst h1
    have h_ne : y ≠ v := Ne.symm h2
    simp [h_ne]
    rw [Array.getElem_set_ne (h:=Fin.val_injective.ne h2)]
  · simp [Fin.val_injective.ne h1]
    intro h; subst h; contradiction
  · simp [Fin.val_injective.ne h1]
    intro h; subst h; contradiction

/- add_edge した後に get をしても整合性が保てるという lemma -/
lemma get_add_edge {n} (g : AdjMat n) (u v x y : Fin n) :
    (g.add_edge u v).get x y =
    (g.get x y || (x = u ∧ y = v) || (x = v ∧ y = u)) := by
  simp only [add_edge]
  rw [get_set_eq]
  rw [get_set_eq]
  by_cases h1 : x = v ∧ y = u
  · simp [h1]
  · by_cases h2 : x = u ∧ y = v
    · simp [h2]
    · simp [h1, h2]

/- add_edge した後に get をしても整合性が保てるという lemma (Prop 版) -/
lemma get_add_edge_Prop {n} (g : AdjMat n) (u v x y : Fin n) :
    (g.add_edge u v).get x y = true ↔
    (g.get x y = true ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  rw [get_add_edge]
  simp [Bool.or_eq_true]
  tauto

/- Get list of isolated vertices (degree = 0) that are not v1 and not in forbidden -/
def get_isolated {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) : List (Fin n) :=
  let all_vertices := List.finRange n
  all_vertices.filter (fun v => g.degree v == 0 && !(v == v1) && !forbidden.elem v)

/- Get list of unused vertices (1 ≤ degree ≤ 3) that are not adjacent to v1,
    not v1, and not in forbidden -/
def get_unused {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) : List (Fin n) :=
  let all_vertices := List.finRange n
  all_vertices.filter (fun v =>
    let deg := g.degree v
    decide (1 <= deg) && decide (deg <= 3) && !g.get v1 v && !(v == v1) && !forbidden.elem v
  )

/-
Generate next graphs logic matching Spec.lean:
1. Identify candidates from isolated vertices and unused vertices.
2. Optimization: If there are isolated vertices, pick ONLY the first one (since they are symmetric).
  Otherwise, use all unused vertices.
3. Apply add_edge.
-/
def generate_next_graphs {n}
  (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) : List (AdjMat n) :=
  let isolated := g.get_isolated v1 forbidden
  let unused := g.get_unused v1 forbidden
  -- Spec.lean の match isolated with | [] => unused | h :: _ => h :: unused に合わせる
  let candidates := match isolated with
    | [] => unused
    | h :: _ => h :: unused
  candidates.map (fun v => g.add_edge v1 v)

/-
Transition: Apply generation to a list of graphs.
Matches Spec.transition (S.flatMap).
-/
def transition {n}
  (S : List (AdjMat n)) (v1 : Fin n) (forbidden : List (Fin n)) : List (AdjMat n) :=
  S.flatMap (fun g => g.generate_next_graphs v1 forbidden)

/-
  Impl側の reduce_iso。
  Spec側と同様に opaque (不透明) な定義として宣言します。
  これにより、Leanの証明器はこの関数の中身を見ず、「何らかのリスト変換関数」として扱います。

  実行時には、@[implemented_by] 属性を使って
  「外部プロセスを呼ぶ実装」や「簡易的な重複排除実装」に差し替えることが可能です。
-/
opaque reduce_iso {n} (S : List (AdjMat n)) (anchors : List (Fin n)) : List (AdjMat n)

/-
  Enumerate Gamma 4_4 implementation matching the provided AdjMat structure.

  Pipeline:
  1. Start with an empty graph.
  2. For each anchor (v1..v4), perform 'transition' multiple times to add edges.
    'forbidden' is used to prevent connecting to other anchors during this phase,
    ensuring we are selecting "anonymous" vertices from the pool.
-/
def enumerate_Gamma_4_4 (n : Nat) (v_list : List (Fin n)) : List (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let S0 := [AdjMat.empty n]
    let all_anchors := [v1, v2, v3, v4]
    -- Helper to get forbidden list for a current anchor (exclude itself)
    -- Assuming we want to avoid connecting to other anchors to prioritize "cloud" vertices
    -- based on the previous context.
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
  | _ => []

end AdjMat
end GraphEnumeration
