import Mathlib

namespace GraphEnumeration

/--
Adjacency Matrix structure for a graph with n vertices.
data[i][j] is true if there is an edge between i and j.
We include a proof that the dimensions are exactly n x n.
-/
structure AdjMat (n : Nat) where
  data : Array (Array Bool)
  h_size : data.size = n ∧ ∀ (i : Fin data.size), (data[i]).size = n

namespace AdjMat

/-- Create an empty graph with n vertices. -/
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

/-- Safe access to the adjacency matrix. -/
def get {n} (g : AdjMat n) (u v : Fin n) : Bool :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  let col_idx : Fin row.size := ⟨v.val, by
    have h : row.size = n := g.h_size.2 row_idx
    rw [h]; exact v.isLt⟩
  row[col_idx]

/-- Private helper to set a value in the matrix. -/
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

/-- Add an edge between u and v (symmetric). -/
def add_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v true
  g1.set v u true

/--
Calculate the degree of a vertex u.
Counts the number of 'true' values in the u-th row.
-/
def degree {n} (g : AdjMat n) (u : Fin n) : Nat :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  row.foldl (fun count b => if b then count + 1 else count) 0

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

end AdjMat
end GraphEnumeration
