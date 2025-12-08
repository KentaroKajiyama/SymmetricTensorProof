import SymmetricTensorProof.GraphEnum.Impl
import SymmetricTensorProof.GraphEnum.Spec
import Mathlib

namespace GraphEnumeration

open SimpleGraph

variable {n : Nat}

/-
Convert our computable AdjMat to the SimpleGraph Model.
We use `fromRel` so it automatically handles symmetry (by taking logical OR)
and irreflexivity (by enforcing u ≠ v).
-/
def toSimpleGraph (g : AdjMat n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => g.get u v)

/-
Helper lemma characterizing the adjacency of the converted graph.
-/
theorem toSimpleGraph_adj (g : AdjMat n) (u v : Fin n) :
  (toSimpleGraph g).Adj u v ↔ (g.get u v ∨ g.get v u) ∧ u ≠ v := by
  simp [toSimpleGraph, and_comm]

/-
Correctness theorem: `add_edge` on AdjMat corresponds to `add_edge` on SimpleGraph.
-/
theorem add_edge_correct (g : AdjMat n) (u v : Fin n) :
  toSimpleGraph (g.add_edge u v) = GraphEnumeration.add_edge (toSimpleGraph g) u v := by
  ext x y
  rw [toSimpleGraph_adj]
  -- Unfold the specification's add_edge
  rw [GraphEnumeration.add_edge]
  rw [SimpleGraph.fromEdgeSet_adj]
  -- Expand the definition of the new edge set
  simp only [Set.mem_union, Set.mem_singleton_iff, SimpleGraph.mem_edgeSet]
  -- Use our implementation lemmas
  rw [AdjMat.get_add_edge, AdjMat.get_add_edge]
  -- Expand SimpleGraph adjacency on the RHS for easier matching
  rw [toSimpleGraph_adj]
  -- Expand Sym2 equality
  rw [Sym2.eq_iff]
  simp only [Bool.or_eq_true, decide_eq_true_iff]
  -- Now the goal is purely propositional logic with equality
  -- LHS: ((getxy ∨ x=u∧y=v ∨ x=v∧y=u) ∨ (getyx ∨ y=u∧x=v ∨ y=v∧x=u)) ∧ x≠y
  -- RHS: ((getxy ∨ getyx) ∧ x≠y) ∨ ((x=u∧y=v ∨ x=v∧y=u) ∧ x≠y)
  -- The structure is effectively a large propositional equivalence.
  constructor
  · rintro ⟨((h_get_xy | h_eq1) | h_eq2) | ((h_get_yx | h_eq3) | h_eq4), h_ne⟩
    · refine ⟨?_, h_ne⟩; left; refine ⟨?_, h_ne⟩; left; exact h_get_xy
    · refine ⟨?_, h_ne⟩; right; left; exact h_eq1
    · refine ⟨?_, h_ne⟩; right; right; exact h_eq2
    · refine ⟨?_, h_ne⟩; left; refine ⟨?_, h_ne⟩; right; exact h_get_yx
    · refine ⟨?_, h_ne⟩; right; right; exact ⟨h_eq3.2, h_eq3.1⟩
    · refine ⟨?_, h_ne⟩; right; left; exact ⟨h_eq4.2, h_eq4.1⟩
  · rintro ⟨(h_get_xy | h_get_yx) | (h_eq1 | h_eq2), h_ne⟩
    · refine ⟨?_, h_ne⟩; left; left; left; exact h_get_xy
    · refine ⟨?_, h_ne⟩; right; left; left; exact h_get_yx
    · refine ⟨?_, h_ne⟩; left; left; right; exact h_eq1
    · refine ⟨?_, h_ne⟩; left; right; exact h_eq2

end GraphEnumeration
