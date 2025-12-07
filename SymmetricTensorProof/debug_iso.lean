import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Order.RelIso.Basic
import Mathlib.Tactic

noncomputable section

namespace DebugIso

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Iso (G H : SimpleGraph V) := RelIso G.Adj H.Adj

structure AnchoredIso (G H : SimpleGraph V) (anchors : List V) extends RelIso G.Adj H.Adj where
  fix_anchors : ∀ v ∈ anchors, toEquiv v = v

open Classical in
def MaxDegree4 (G : SimpleGraph V) : Prop :=
  ∀ v, (G.neighborFinset v).card ≤ 4

lemma AnchoredIso.max_degree_iff {G H : SimpleGraph V} {anchors : List V}
  (iso : AnchoredIso G H anchors) : MaxDegree4 G ↔ MaxDegree4 H := by
  unfold MaxDegree4
  constructor
  · intro h v
    have h_card : (H.neighborFinset v).card = (G.neighborFinset (iso.toEquiv.symm v)).card := by
      apply Finset.card_bij (fun x _ => iso.toEquiv.symm x)
      · intro x hx
        simp only [SimpleGraph.mem_neighborFinset] at hx ⊢
        rw [←iso.toRelIso.apply_symm_apply x, ←iso.toRelIso.apply_symm_apply v] at hx
        rw [iso.toRelIso.map_rel_iff] at hx
        exact hx
      · intro x y _ _ hxy
        exact iso.toEquiv.symm.injective hxy
      · intro y hy
        simp only [SimpleGraph.mem_neighborFinset] at hy ⊢
        exists iso.toEquiv y
        constructor
        -- Here we want to see the goals
        · rw [←iso.toRelIso.map_rel_iff]; simp; exact hy
        · simp
    rw [h_card]
    apply h
  · intro h v
    sorry
