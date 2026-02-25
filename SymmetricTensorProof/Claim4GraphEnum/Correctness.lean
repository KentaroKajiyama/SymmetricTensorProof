import SymmetricTensorProof.Claim4GraphEnum.Impl
import SymmetricTensorProof.Claim4GraphEnum.Spec
import Mathlib

set_option linter.style.longLine false

namespace Claim4GraphEnum.Correctness

open SimpleGraph Claim4GraphEnum.Spec Claim4GraphEnum.Impl

variable {n : Nat}

-- ============================================================
-- 1. toSimpleGraph ブリッジ関数
-- ============================================================

def toSimpleGraph (g : AdjMat n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun u v => g.get u v)

theorem toSimpleGraph_adj (g : AdjMat n) (u v : Fin n) :
  (toSimpleGraph g).Adj u v ↔ (g.get u v ∨ g.get v u) ∧ u ≠ v := by
  simp [toSimpleGraph, and_comm]

instance (g : AdjMat n) : DecidableRel (toSimpleGraph g).Adj := by
  intro u v; rw [toSimpleGraph_adj]; infer_instance

-- ============================================================
-- 2. adj_iff_get
-- ============================================================

theorem adj_iff_get (g : AdjMat n) (u v : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, g.get a a = false) :
    (toSimpleGraph g).Adj u v ↔ g.get u v = true := by
  rw [toSimpleGraph_adj]
  by_cases h_eq : u = v
  · subst h_eq; simp [h_irref]
  · constructor
    · rintro ⟨h | h, _⟩
      · exact h
      · rwa [h_symm] at h
    · intro h; exact ⟨Or.inl h, h_eq⟩

-- ============================================================
-- 3. Valid 述語
-- ============================================================

def Valid {n} (g : AdjMat n) : Prop :=
  (∀ u v, g.get u v = g.get v u) ∧ (∀ u, g.get u u = false)

theorem valid_empty {n} : Valid (AdjMat.empty n) := by
  constructor
  · intro u v; simp [AdjMat.empty, AdjMat.get, Array.getElem_replicate]
  · intro u; simp [AdjMat.empty, AdjMat.get, Array.getElem_replicate]

theorem valid_add_edge {n} {g : AdjMat n} {u v : Fin n}
    (h_valid : Valid g) (h_ne : u ≠ v) : Valid (g.add_edge u v) := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · -- 対称性: Bool 等式
    -- ゴール: g.get x y || decide(x=u∧y=v) || decide(x=v∧y=u)
    --       = g.get y x || decide(y=u∧x=v) || decide(y=v∧x=u)
    -- decide(x=u∧y=v) = decide(y=v∧x=u) by and_comm, and similar for the other term
    simp only [AdjMat.get_add_edge]
    rw [h_valid.1 x y]
    simp [and_comm, Bool.or_comm, Bool.or_left_comm]
  · -- 非反射性
    simp only [AdjMat.get_add_edge, h_valid.2 x, Bool.false_or,
      Bool.or_eq_false_iff, decide_eq_false_iff_not, not_and]
    exact ⟨fun h1 h2 => h_ne (h1 ▸ h2), fun h1 h2 => h_ne (h2 ▸ h1)⟩

theorem valid_remove_edge {n} {g : AdjMat n} {u v : Fin n}
    (h_valid : Valid g) : Valid (g.remove_edge u v) := by
  constructor
  · intro x y
    simp only [AdjMat.remove_edge, AdjMat.get_set_eq]
    split_ifs <;> try rfl
    all_goals (try rw [h_valid.1 x y])
    all_goals simp_all
  · intro x
    simp only [AdjMat.remove_edge, AdjMat.get_set_eq]
    split_ifs <;> try rfl
    all_goals (try exact h_valid.2 x)

-- ============================================================
-- 4. add_edge の正当性
-- ============================================================

theorem add_edge_correct (g : AdjMat n) (u v : Fin n) (h_ne : u ≠ v) :
    toSimpleGraph (g.add_edge u v) =
    Claim4GraphEnum.Spec.add_edge (toSimpleGraph g) u v h_ne := by
  ext x y
  constructor
  · -- LHS → RHS
    intro h_lhs
    -- Spec.add_edge.Adj の定義: G.Adj x y ∨ (x=u∧y=v) ∨ (x=v∧y=u)
    change (toSimpleGraph g).Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)
    rw [toSimpleGraph_adj] at h_lhs
    -- h_lhs : ((g.add_edge u v).get x y ∨ (g.add_edge u v).get y x) ∧ x ≠ y
    obtain ⟨h_get | h_get, hne⟩ := h_lhs
    · -- h_get : (g.add_edge u v).get x y = true
      -- Bool.or_eq_true で展開後は ((A || B) = true ∨ C = true) の形式
      simp only [AdjMat.get_add_edge, Bool.or_eq_true, decide_eq_true_iff] at h_get
      -- h_get : (g.get x y = true ∨ (x=u∧y=v)) ∨ (x=v∧y=u)
      rcases h_get with ((h | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      · exact Or.inl ((toSimpleGraph_adj g x y).mpr ⟨Or.inl h, hne⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
    · -- h_get : (g.add_edge u v).get y x = true
      simp only [AdjMat.get_add_edge, Bool.or_eq_true, decide_eq_true_iff] at h_get
      -- h_get : (g.get y x = true ∨ (y=u∧x=v)) ∨ (y=v∧x=u)
      rcases h_get with ((h | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩)
      · exact Or.inl ((toSimpleGraph_adj g x y).mpr ⟨Or.inr h, hne⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · -- RHS → LHS
    intro h_rhs
    show (toSimpleGraph (g.add_edge u v)).Adj x y
    rw [toSimpleGraph_adj]
    -- ゴール: ((g.add_edge u v).get x y ∨ (g.add_edge u v).get y x) ∧ x ≠ y
    simp only [AdjMat.get_add_edge, Bool.or_eq_true, decide_eq_true_iff]
    -- ゴール: ((g.get x y = true ∨ (x=u∧y=v)) ∨ (x=v∧y=u)) ∨ ...
    change (toSimpleGraph g).Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) at h_rhs
    rcases h_rhs with hadj | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [toSimpleGraph_adj] at hadj
      obtain ⟨h | h, hne⟩ := hadj
      · exact ⟨Or.inl (Or.inl (Or.inl h)), hne⟩
      · exact ⟨Or.inr (Or.inl (Or.inl h)), hne⟩
    · exact ⟨Or.inl (Or.inl (Or.inr ⟨rfl, rfl⟩)), h_ne⟩
    · exact ⟨Or.inl (Or.inr ⟨rfl, rfl⟩), h_ne.symm⟩

-- ============================================================
-- 5. degree の正当性
-- ============================================================

theorem degree_correct (g : AdjMat n) (u : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, g.get a a = false) :
    g.degree u = ((toSimpleGraph g).neighborFinset u).card := by
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  have h_deg_eq_card :
    g.degree u = (Finset.filter (fun v ↦ g.get u v) Finset.univ).card := by
    sorry
  rw [h_deg_eq_card]
  congr 1; ext v
  rw [SimpleGraph.mem_neighborFinset, toSimpleGraph_adj]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h_get
    exact ⟨Or.inl h_get, fun h_eq => by rw [h_eq] at h_get; simp [h_irref] at h_get⟩
  · rintro ⟨h | h, _⟩
    · exact h
    · rwa [h_symm]

-- ============================================================
-- 6. neighbors の正当性
-- ============================================================

theorem neighbors_correct (g : AdjMat n) (u : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, g.get a a = false) :
    (g.neighbors u).toFinset = (toSimpleGraph g).neighborFinset u := by
  ext v
  simp only [AdjMat.neighbors, List.mem_toFinset, List.mem_filter, List.mem_finRange,
    true_and, SimpleGraph.mem_neighborFinset]
  exact (adj_iff_get g u v h_symm h_irref).symm

theorem list_filter_length_eq_sum_ones {α} (l : List α) (p : α → Bool) :
  (l.filter (fun x => p x)).length = (l.map (fun x => if p x then 1 else 0)).sum := by
  induction l with
  | nil => rfl
  | cons h t ih =>
    simp only [List.filter_cons, List.map_cons, List.sum_cons]
    split_ifs with hp
    · simp only [List.length_cons]
      omega
    · omega

theorem degree_eq_neighbors_length (g : AdjMat n) (u : Fin n) :
    g.degree u = (g.neighbors u).length := by
  sorry

lemma degree_congr_dec {n} {G : SimpleGraph (Fin n)} {v : Fin n}
    (d1 d2 : DecidableRel G.Adj) :
    @SimpleGraph.degree (Fin n) G v (@SimpleGraph.neighborSetFintype (Fin n) G _ d1 v) =
    @SimpleGraph.degree (Fin n) G v (@SimpleGraph.neighborSetFintype (Fin n) G _ d2 v) := by
  congr 1
  apply Subsingleton.elim

lemma degree_congr {n} {G1 G2 : SimpleGraph (Fin n)} (h : G1 = G2) (u : Fin n)
    [d1 : DecidableRel G1.Adj] [d2 : DecidableRel G2.Adj] :
    G1.degree u = G2.degree u := by
  subst h
  exact degree_congr_dec d1 d2

-- ============================================================
-- 7. 空グラフの正当性
-- ============================================================

lemma empty_correct : toSimpleGraph (AdjMat.empty n) = ⊥ := by
  ext u v; simp [toSimpleGraph, SimpleGraph.fromRel, AdjMat.empty, AdjMat.get]

-- ============================================================
-- 8. apply_method* の Valid 保存補題
-- ============================================================

lemma ite_some_none_eq_some_iff {α} {cond : Bool} {b a : α} :
    ((if cond then some b else none) = some a) ↔ (cond = true ∧ b = a) := by
  cases cond <;> simp

lemma ite_some_none_eq_some_prop_iff {α} {P : Prop} [Decidable P] {b a : α} :
    ((if P then some b else none) = some a) ↔ (P ∧ b = a) := by
  split_ifs with h <;> simp [h]

lemma valid_foldl_add_edge_pair {n α} (l : List α) (g0 : AdjMat n) (u v : α → Fin n)
    (h_valid : Valid g0) (h_ne : ∀ a ∈ l, u a ≠ v a) :
    Valid (l.foldl (fun acc a => acc.add_edge (u a) (v a)) g0) := by
  induction l generalizing g0 with
  | nil => exact h_valid
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    · apply valid_add_edge h_valid
      exact h_ne hd (List.Mem.head _)
    · intro a ha
      exact h_ne a (List.mem_cons_of_mem hd ha)

lemma apply_method2_preserves_valid {n} {g : AdjMat n}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_method2 g, Valid g' := by
  intro g' hg'
  simp only [AdjMat.apply_method2, List.mem_map] at hg'
  obtain ⟨⟨u, v⟩, hmem, rfl⟩ := hg'
  apply valid_add_edge h_valid
  -- u ≠ v: hmem から u.val < v.val を導いて u ≠ v を示す
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_finRange, true_and] at hmem
  obtain ⟨u', _, v', _, hfmap⟩ := hmem
  revert hfmap
  split
  · rename_i hcond
    intro hfmap
    simp only [Option.some.injEq, Prod.mk.injEq] at hfmap
    obtain ⟨h_u, h_v⟩ := hfmap
    subst u' v'
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hcond
    exact Fin.ne_of_lt hcond.1
  · intro hfmap
    cases hfmap

lemma split_vertex_preserves_valid {n} {g : AdjMat n} (w : Fin n) (N1 N2 : List (Fin n))
    (_h_valid : Valid g) (hN1 : ∀ x ∈ N1, x ≠ w) :
    Valid (AdjMat.split_vertex g w N1 N2) := by
  simp only [AdjMat.split_vertex]
  apply valid_add_edge
  · apply valid_foldl_add_edge_pair
    · apply valid_foldl_add_edge_pair
      · apply valid_foldl_add_edge_pair
        · exact valid_empty
        · intro a h_mem
          simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and,
            ite_some_none_eq_some_iff] at h_mem
          obtain ⟨i, j, hcond, rfl⟩ := h_mem
          simp only [Bool.and_eq_true, decide_eq_true_iff] at hcond
          exact Fin.ne_of_lt hcond.1.1.1
      · intro x hx hc
        have h_eq : w = x := Fin.castSucc_inj.mp hc
        exact hN1 x hx h_eq.symm
    · intro x hx hc
      have hx_lt := x.isLt
      have heq : x.val = n := by
        have h1 : (Fin.castSucc x).val = x.val := rfl
        have h2 : (Fin.last n).val = n := rfl
        rw [Fin.ext_iff, h1, h2] at hc
        exact hc.symm
      omega
  · intro hc
    have hw_lt := w.isLt
    have heq : w.val = n := by
      have h1 : (Fin.castSucc w).val = w.val := rfl
      have h2 : (Fin.last n).val = n := rfl
      rw [Fin.ext_iff, h1, h2] at hc
      exact hc
    omega

lemma mem_partitions_of_4_left {α} {l N1 N2 : List α} {x : α}
    (h : (N1, N2) ∈ AdjMat.partitions_of_4 l) (hx : x ∈ N1) : x ∈ l := by
  unfold AdjMat.partitions_of_4 at h
  split at h
  · rename_i a b c d _
    simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, or_false] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (Or.inr rfl))
  · contradiction

lemma apply_method3b_preserves_valid {n} {g : AdjMat n}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_method3b g, Valid g' := by
  intro g' hg'
  simp only [AdjMat.apply_method3b, List.mem_flatMap, List.mem_filter,
    List.mem_finRange, true_and, List.mem_map] at hg'
  obtain ⟨w, _, parts, hparts, rfl⟩ := hg'
  -- parts ∈ partitions_of_4 (g.neighbors w)
  -- we know parts is a pair (N1, N2) where N1 ++ N2 is a permutation of neighbors w.
  -- thus every x in N1 is in neighbors w, so g.get w x = true, so x ≠ w (since Valid g)
  obtain ⟨N1, N2⟩ := parts
  apply split_vertex_preserves_valid w N1 N2 h_valid
  intro x hx
  have h_in_neighbors : x ∈ g.neighbors w := mem_partitions_of_4_left hparts hx
  simp only [AdjMat.neighbors, List.mem_filter, List.mem_finRange, true_and] at h_in_neighbors
  intro hc
  subst x
  have h_irref := h_valid.2 w
  rw [h_in_neighbors] at h_irref
  contradiction

lemma valid_of_mem_flatMap {n α} {l : List α} {f : α → List (AdjMat n)} {g : AdjMat n}
    (h_mem : g ∈ l.flatMap f)
    (h_valid : ∀ (a : α), a ∈ l → ∀ (g' : AdjMat n), g' ∈ f a → Valid g') : Valid g := by
  simp only [List.mem_flatMap] at h_mem
  rcases h_mem with ⟨a, ha, hg⟩
  exact h_valid a ha g hg

lemma valid_of_mem_filterMap {n α} {l : List α} {f : α → Option (AdjMat n)} {g : AdjMat n}
    (h_mem : g ∈ l.filterMap f)
    (h_valid : ∀ (a : α), a ∈ l → f a = some g → Valid g) : Valid g := by
  simp only [List.mem_filterMap] at h_mem
  rcases h_mem with ⟨a, ha, hg⟩
  exact h_valid a ha hg

lemma valid_of_mem_map {n α} {l : List α} {f : α → AdjMat n} {g : AdjMat n}
    (h_mem : g ∈ l.map f)
    (h_valid : ∀ (a : α), a ∈ l → Valid (f a)) : Valid g := by
  simp only [List.mem_map] at h_mem
  rcases h_mem with ⟨a, ha, rfl⟩
  exact h_valid a ha

lemma apply_method1_preserves_valid {n} {g : AdjMat n}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_method1 g, Valid g' := by
  intro g' hg'
  unfold AdjMat.apply_method1 at hg'
  apply valid_of_mem_flatMap hg'; intro a h_a g' hg'
  rcases a with ⟨v1, v2⟩
  dsimp only at hg'
  split at hg'
  · rename_i x1a x1b x2a x2b heq_X1 heq_X2
    apply valid_of_mem_map hg'; intro ⟨⟨a1, b1⟩, ⟨a2, b2⟩⟩ h_ab
    have h_a1_b1_a2_b2 : a1 ∈ [x1a, x1b] ∧ a2 ∈ [x2a, x2b] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h_ab
      rcases h_ab with h | h | h | h <;> (
        simp only [Prod.mk.injEq] at h; obtain ⟨⟨rfl, _⟩, ⟨rfl, _⟩⟩ := h; simp)
    have ha1_neigh : a1 ∈ g.neighbors v1 := by
      have h := h_a1_b1_a2_b2.1
      rw [← heq_X1] at h
      simp only [List.mem_filter] at h
      exact h.1
    have ha2_neigh : a2 ∈ g.neighbors v2 := by
      have h := h_a1_b1_a2_b2.2
      rw [← heq_X2] at h
      simp only [List.mem_filter] at h
      exact h.1
    repeat apply valid_add_edge
    · apply valid_foldl_add_edge_pair
      · apply valid_foldl_add_edge_pair
        · exact valid_empty
        · intro a ha
          simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and,
            ite_some_none_eq_some_iff] at ha
          obtain ⟨i, j, hcond, rfl⟩ := ha
          simp only [Bool.and_eq_true, decide_eq_true_iff] at hcond
          exact Fin.ne_of_lt hcond.1.1.1.1.1
      · intro a ha
        simp only [List.mem_flatMap, List.mem_filterMap, ite_some_none_eq_some_prop_iff] at ha
        obtain ⟨i, hi, j, hj, hcond, rfl⟩ := ha
        exact Fin.ne_of_lt hcond
    · intro hc
      have h1 : (Fin.castAdd 2 v1).val = v1.val := rfl
      have h2 : (Fin.castAdd 2 a1).val = a1.val := rfl
      rw [Fin.ext_iff, h1, h2] at hc
      have heq : v1 = a1 := Fin.ext hc
      rw [heq] at ha1_neigh
      simp only [AdjMat.neighbors, List.mem_filter, List.mem_finRange, true_and] at ha1_neigh
      have hirref := h_valid.2 a1
      rw [ha1_neigh] at hirref
      contradiction
    · intro hc
      have h_u3 : (⟨n, by omega⟩ : Fin (n+2)).val = n := rfl
      have h_b1 : (Fin.castAdd 2 b1).val = b1.val := rfl
      rw [Fin.ext_iff, h_u3, h_b1] at hc
      have hb1_lt := b1.isLt
      omega
    · intro hc
      have h1 : (Fin.castAdd 2 v2).val = v2.val := rfl
      have h2 : (Fin.castAdd 2 a2).val = a2.val := rfl
      rw [Fin.ext_iff, h1, h2] at hc
      have heq : v2 = a2 := Fin.ext hc
      rw [heq] at ha2_neigh
      simp only [AdjMat.neighbors, List.mem_filter, List.mem_finRange, true_and] at ha2_neigh
      have hirref := h_valid.2 a2
      rw [ha2_neigh] at hirref
      contradiction
    · intro hc
      have h_u4 : (⟨n+1, by omega⟩ : Fin (n+2)).val = n+1 := rfl
      have h_b2 : (Fin.castAdd 2 b2).val = b2.val := rfl
      rw [Fin.ext_iff, h_u4, h_b2] at hc
      have hb2_lt := b2.isLt
      omega
  · contradiction

lemma apply_inv_method2_preserves_valid {n} {g : AdjMat n}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_inv_method2 g, Valid g' := by
  intro g' hg'
  simp only [AdjMat.apply_inv_method2, List.mem_map] at hg'
  obtain ⟨⟨u, v⟩, _, rfl⟩ := hg'
  exact valid_remove_edge h_valid

lemma apply_inv_method3b_preserves_valid {n} {g : AdjMat (n + 1)}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_inv_method3b g, Valid g' := by
  intro g' hg'
  unfold AdjMat.apply_inv_method3b at hg'
  split at hg'
  · simp_all
  · apply valid_of_mem_filterMap hg'; intro a h_a heq
    simp only [List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and, ite_some_none_eq_some_iff] at h_a
    obtain ⟨u, _, v, _, h_cond, rfl⟩ := h_a
    simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
    have h_u_lt_v : u.val < v.val := h_cond.left
    have hu_lt := u.isLt; have hv_lt := v.isLt
    dsimp only at heq
    have h_eval : (((g.neighbors u).filter (fun x => x != v)).any (fun x => ((g.neighbors v).filter (fun y => y != u)).contains x)) = true ∨
                  (((g.neighbors u).filter (fun x => x != v)).any (fun x => ((g.neighbors v).filter (fun y => y != u)).contains x)) = false := by
      cases (((g.neighbors u).filter (fun x => x != v)).any (fun x => ((g.neighbors v).filter (fun y => y != u)).contains x))
      · exact Or.inr rfl
      · exact Or.inl rfl
    rcases h_eval with h_shared | h_shared
    · rw [h_shared] at heq
      contradiction
    · rw [h_shared] at heq
      simp at heq
      symm at heq; subst g'
      apply valid_foldl_add_edge_pair
      · apply valid_foldl_add_edge_pair
        · apply valid_foldl_add_edge_pair
          · exact valid_empty
          · intro a ha
            simp only [List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and] at ha
            obtain ⟨i, j, h_eq⟩ := ha
            split_ifs at h_eq with hcond
            simp only [Option.some.injEq] at h_eq
            subst a
            obtain ⟨⟨⟨⟨⟨h_lt, h_neq_iu⟩, h_neq_iv⟩, h_neq_ju⟩, h_neq_jv⟩, h_get⟩ := hcond
            intro hc
            dsimp only at hc
            have h_eq := Fin.ext_iff.mp hc
            change (if i = u ∨ i = v then n - 1 else if i < u then ↑i else if i < v then ↑i - 1 else ↑i - 2) % n = (if j = u ∨ j = v then n - 1 else if j < u then ↑j else if j < v then ↑j - 1 else ↑j - 2) % n at h_eq
            clear hc
            have h_i_iff : (i = u ∨ i = v) ↔ False := ⟨by rintro (rfl | rfl); exact h_neq_iu rfl; exact h_neq_iv rfl, False.elim⟩
            have h_j_iff : (j = u ∨ j = v) ↔ False := ⟨by rintro (rfl | rfl); exact h_neq_ju rfl; exact h_neq_jv rfl, False.elim⟩
            simp only [h_i_iff, h_j_iff, ite_false] at h_eq
            have hiu : i.val ≠ u.val := fun h => h_neq_iu (Fin.ext h)
            have hiv : i.val ≠ v.val := fun h => h_neq_iv (Fin.ext h)
            have hju : j.val ≠ u.val := fun h => h_neq_ju (Fin.ext h)
            have hjv : j.val ≠ v.val := fun h => h_neq_jv (Fin.ext h)
            have hilj : i.val < j.val := by simpa using h_lt
            have hulv : u.val < v.val := h_u_lt_v
            have h_mod_i : ((if i < u then ↑i else if i < v then ↑i - 1 else ↑i - 2) : ℕ) % n = ((if i < u then ↑i else if i < v then ↑i - 1 else ↑i - 2) : ℕ) := by apply Nat.mod_eq_of_lt; split_ifs <;> omega
            have h_mod_j : ((if j < u then ↑j else if j < v then ↑j - 1 else ↑j - 2) : ℕ) % n = ((if j < u then ↑j else if j < v then ↑j - 1 else ↑j - 2) : ℕ) := by apply Nat.mod_eq_of_lt; split_ifs <;> omega
            rw [h_mod_i, h_mod_j] at h_eq
            revert h_eq
            split_ifs <;> intro h_eq <;> omega
        · intro a ha
          intro hc
          have ha_lt := a.isLt; have hu_lt := u.isLt; have hv_lt := v.isLt
          have h_eq := Fin.ext_iff.mp hc
          change n - 1 = (if a = u ∨ a = v then n - 1 else if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) % n at h_eq
          clear hc
          simp only [AdjMat.neighbors, List.mem_filter, List.mem_finRange, true_and, bne_iff_ne] at ha
          have h_neq : a ≠ v := ha.2
          have h_neq_u : a ≠ u := by intro h; subst a; have hirref := h_valid.2 u; rw [ha.1] at hirref; contradiction
          have h_a_iff : (a = u ∨ a = v) ↔ False := ⟨by rintro (rfl | rfl); exact h_neq_u rfl; exact h_neq rfl, False.elim⟩
          simp only [h_a_iff, ite_false] at h_eq
          have hau : a.val ≠ u.val := fun h => h_neq_u (Fin.ext h)
          have hav : a.val ≠ v.val := fun h => h_neq (Fin.ext h)
          have hulv : u.val < v.val := h_u_lt_v
          have h_mod_a : ((if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) : ℕ) % n = ((if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) : ℕ) := by apply Nat.mod_eq_of_lt; split_ifs <;> omega
          rw [h_mod_a] at h_eq
          revert h_eq
          split_ifs <;> intro h_eq <;> omega
      · intro a ha
        intro hc
        have ha_lt := a.isLt; have hu_lt := u.isLt; have hv_lt := v.isLt
        have h_eq := Fin.ext_iff.mp hc
        change n - 1 = (if a = u ∨ a = v then n - 1 else if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) % n at h_eq
        clear hc
        simp only [AdjMat.neighbors, List.mem_filter, List.mem_finRange, true_and, bne_iff_ne] at ha
        have h_neq : a ≠ u := ha.2
        have h_neq_v : a ≠ v := by intro h; subst a; have hirref := h_valid.2 v; rw [ha.1] at hirref; contradiction
        have h_a_iff : (a = u ∨ a = v) ↔ False := ⟨by rintro (rfl | rfl); exact h_neq rfl; exact h_neq_v rfl, False.elim⟩
        simp only [h_a_iff, ite_false] at h_eq
        have hau : a.val ≠ u.val := fun h => h_neq (Fin.ext h)
        have hav : a.val ≠ v.val := fun h => h_neq_v (Fin.ext h)
        have hulv : u.val < v.val := h_u_lt_v
        have h_mod_a : ((if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) : ℕ) % n = ((if a < u then ↑a else if a < v then ↑a - 1 else ↑a - 2) : ℕ) := by apply Nat.mod_eq_of_lt; split_ifs <;> omega
        rw [h_mod_a] at h_eq
        revert h_eq
        split_ifs <;> intro h_eq <;> omega

lemma countP_lt_le {u_list : List Nat} (h_nodup : u_list.Nodup) (i : Nat) :
    u_list.countP (fun u => u < i) ≤ i := by
  -- Number of unique natural numbers < i is at most i
  sorry

lemma countP_lt_diff {u_list : List Nat} (h_nodup : u_list.Nodup) (i j : Nat)
    (hi : i ∉ u_list) (hj : j ∉ u_list) (h_lt : i < j) :
    i - u_list.countP (fun u => u < i) < j - u_list.countP (fun u => u < j) := by
  -- Monotonicity of the difference function for a set of missing elements
  sorry

lemma map_idx_lt_n_minus_2 {n} (hn : n ≥ 2) (u1 u2 u3 u4 x : Fin (n + 2))
    (h_nodup : List.Nodup [u1.val, u2.val, u3.val, u4.val])
    (hx1 : x ≠ u1) (hx2 : x ≠ u2) (hx3 : x ≠ u3) (hx4 : x ≠ u4) :
    let u_list := [u1.val, u2.val, u3.val, u4.val]
    let less_count := u_list.countP (fun u_val => u_val < x.val)
    x.val - less_count < n - 2 := by
  -- Follows from x < n+2 and exactly 4 elements excluded
  sorry

lemma map_idx_inj_Prop {n} (hn : n ≥ 2) (u1 u2 u3 u4 : Fin (n + 2))
    (h_nodup : List.Nodup [u1.val, u2.val, u3.val, u4.val])
    (i j : Fin (n + 2))
    (hi1 : i ≠ u1) (hi2 : i ≠ u2) (hi3 : i ≠ u3) (hi4 : i ≠ u4)
    (hj1 : j ≠ u1) (hj2 : j ≠ u2) (hj3 : j ≠ u3) (hj4 : j ≠ u4)
    (h_lt : i.val < j.val) :
    let u_list := [u1.val, u2.val, u3.val, u4.val]
    let less_i := u_list.countP (fun u_val => u_val < i.val)
    let less_j := u_list.countP (fun u_val => u_val < j.val)
    i.val - less_i < j.val - less_j := by
  let u_list := [u1.val, u2.val, u3.val, u4.val]
  have hi : i.val ∉ u_list := by
    simp [u_list]
    exact ⟨fun h => hi1 (Fin.ext h), fun h => hi2 (Fin.ext h), fun h => hi3 (Fin.ext h), fun h => hi4 (Fin.ext h)⟩
  have hj : j.val ∉ u_list := by
    simp [u_list]
    exact ⟨fun h => hj1 (Fin.ext h), fun h => hj2 (Fin.ext h), fun h => hj3 (Fin.ext h), fun h => hj4 (Fin.ext h)⟩
  exact countP_lt_diff h_nodup i.val j.val hi hj h_lt

lemma apply_inv_method1_preserves_valid {n} {g : AdjMat (n + 2)}
    (h_valid : Valid g) :
    ∀ g' ∈ AdjMat.apply_inv_method1 g, Valid g' := by
  sorry

-- ============================================================
-- 9. Method 2 (辺の付加) の正当性
-- ============================================================

theorem apply_method2_sound (g : AdjMat n) (g' : AdjMat n)
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_method2 g →
    Claim4GraphEnum.Spec.Method2_Rel (toSimpleGraph g) (toSimpleGraph g') := by
  intro hmem
  simp only [AdjMat.apply_method2, List.mem_map] at hmem
  obtain ⟨⟨u, v⟩, hmem_pair, rfl⟩ := hmem
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_filter,
    List.mem_finRange, true_and] at hmem_pair
  obtain ⟨u', hdeg_u, v', hdeg_v, hfmap⟩ := hmem_pair
  revert hfmap
  split
  · rename_i hcond
    intro hfmap
    simp only [Option.some.injEq, Prod.mk.injEq] at hfmap
    obtain ⟨h_u, h_v⟩ := hfmap
    subst u' v'
    simp only [Bool.and_eq_true, decide_eq_true_iff] at hcond
    have h_ne : u ≠ v := Fin.ne_of_lt (Fin.mk_lt_mk.mpr hcond.1)
    have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
    rw [beq_iff_eq] at hdeg_u hdeg_v
    have h_deg_u : (toSimpleGraph g).degree u = 3 := by
      rw [SimpleGraph.degree, ← degree_correct g u h_valid.1 h_irref]; exact hdeg_u
    have h_deg_v : (toSimpleGraph g).degree v = 3 := by
      rw [SimpleGraph.degree, ← degree_correct g v h_valid.1 h_irref]; exact hdeg_v
    have h_not_adj : ¬(toSimpleGraph g).Adj u v := by
      rw [adj_iff_get g u v h_valid.1 h_irref]
      intro hc
      revert hcond
      simp [hc]
    refine ⟨u, v, h_ne, ?_, ?_, h_not_adj, add_edge_correct g u v h_ne⟩
    · convert h_deg_u
    · convert h_deg_v
  · intro hfmap
    cases hfmap

theorem apply_method2_complete (g : AdjMat n)
    (G' : SimpleGraph (Fin n))
    (h_valid : Valid g) :
    Claim4GraphEnum.Spec.Method2_Rel (toSimpleGraph g) G' →
    ∃ g' ∈ AdjMat.apply_method2 g, toSimpleGraph g' = G' := by
  intro hrel
  obtain ⟨u, v, h_neq, h_deg_u, h_deg_v, h_not_adj, rfl⟩ := hrel
  by_cases h_lt : u < v
  · use g.add_edge u v
    constructor
    · simp only [AdjMat.apply_method2, List.mem_map,
        List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and]
      use (u, v)
      refine ⟨?_, rfl⟩
      have hu_eq : (g.degree u == 3) = true := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        have hdeg := degree_correct g u h_valid.1 h_irref
        rw [beq_iff_eq, hdeg, ← SimpleGraph.degree]
        convert h_deg_u
      use u; refine ⟨hu_eq, ?_⟩
      have hv_eq : (g.degree v == 3) = true := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        have hdeg := degree_correct g v h_valid.1 h_irref
        rw [beq_iff_eq, hdeg, ← SimpleGraph.degree]
        convert h_deg_v
      use v; refine ⟨hv_eq, ?_⟩
      have h1 : ¬ g.get u v := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        rw [← adj_iff_get g u v h_valid.1 h_irref]
        exact h_not_adj
      simp [h_lt, h1]
    · exact add_edge_correct g u v h_neq
  · have h_lt' : v < u := by
      have := Fin.lt_or_lt_of_ne h_neq
      tauto
    use g.add_edge v u
    constructor
    · simp only [AdjMat.apply_method2, List.mem_map, List.mem_flatMap,
        List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and]
      use (v, u)
      refine ⟨?_, rfl⟩
      have hv_eq : (g.degree v == 3) = true := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        have hdeg := degree_correct g v h_valid.1 h_irref
        rw [beq_iff_eq, hdeg, ← SimpleGraph.degree]
        convert h_deg_v
      use v; refine ⟨hv_eq, ?_⟩
      have hu_eq : (g.degree u == 3) = true := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        have hdeg := degree_correct g u h_valid.1 h_irref
        rw [beq_iff_eq, hdeg, ← SimpleGraph.degree]
        convert h_deg_u
      use u; refine ⟨hu_eq, ?_⟩
      have h1 : ¬ g.get v u := by
        have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
        rw [← adj_iff_get g v u h_valid.1 h_irref]
        intro hc; apply h_not_adj; exact SimpleGraph.Adj.symm hc
      simp [h_lt', h1]
    · have h_symm :
        add_edge (toSimpleGraph g) u v h_neq = add_edge (toSimpleGraph g) v u (Ne.symm h_neq) := by
        ext x y
        simp only [Claim4GraphEnum.Spec.add_edge]
        tauto
      rw [h_symm]
      exact add_edge_correct g v u (Ne.symm h_neq)

-- Helper: neighbors list has no duplicates
lemma neighbors_nodup (g : AdjMat n) (u : Fin n) : (g.neighbors u).Nodup := by
  unfold AdjMat.neighbors
  exact List.Nodup.filter _ (List.nodup_finRange n)

-- Helper: membership in neighbors iff get = true
lemma mem_neighbors_iff (g : AdjMat n) (u v : Fin n) :
    v ∈ g.neighbors u ↔ g.get u v = true := by
  simp [AdjMat.neighbors, List.mem_filter, List.mem_finRange]

-- Helper: the neighborFinset equals the toFinset of the neighbors list
lemma neighborFinset_eq_of_valid (g : AdjMat n) (u : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, g.get a a = false) :
    (toSimpleGraph g).neighborFinset u = (g.neighbors u).toFinset := by
  ext v
  simp only [SimpleGraph.mem_neighborFinset, List.mem_toFinset, mem_neighbors_iff]
  exact adj_iff_get g u v h_symm h_irref

-- Helper: from nodup list [a,b,c,d], extract all 6 pairwise distinctions
lemma nodup_four_distinct {α} {a b c d : α} (h : List.Nodup [a, b, c, d]) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
    and_true] at h
  push_neg at h
  tauto

-- Helper: adjacency in split_vertex for the v1-v2 edge
lemma split_vertex_adj_v1_v2 (g : AdjMat n) (w : Fin n) (N1 N2 : List (Fin n))
    (h_valid : Valid g) :
    (toSimpleGraph (AdjMat.split_vertex g w N1 N2)).Adj
        (Fin.castSucc w) (Fin.last n) := by
  -- split_vertex ends with add_edge v1 v2 = add_edge (castSucc w) (last n)
  -- So the resulting graph has edge (castSucc w, last n)
  have h_ne : Fin.castSucc w ≠ Fin.last n := by
    intro h
    have : (Fin.castSucc w).val = (Fin.last n).val := congrArg Fin.val h
    simp [Fin.val_castSucc, Fin.val_last] at this
    omega
  rw [toSimpleGraph_adj]
  constructor
  · apply Or.inl
    -- The final add_edge (castSucc w) (last n) sets this entry to true
    simp only [AdjMat.split_vertex]
    rw [AdjMat.get_add_edge]
    simp [Fin.ext_iff]
  · exact h_ne

-- Helper: get for split_vertex in terms of the original graph
lemma split_vertex_get_old (g : AdjMat n) (w : Fin n) (N1 N2 : List (Fin n))
    (h_valid : Valid g) (h_N1 : ∀ x ∈ N1, x ≠ w) (h_N2 : ∀ x ∈ N2, x ≠ w)
    (x y : Fin n) (hxw : x ≠ w) (hyw : y ≠ w) :
    (toSimpleGraph (AdjMat.split_vertex g w N1 N2)).Adj
        (Fin.castSucc x) (Fin.castSucc y) ↔
      (toSimpleGraph g).Adj x y := by
  sorry

lemma split_vertex_get_v1_N1 (g : AdjMat n) (w : Fin n) (N1 N2 : List (Fin n))
    (h_valid : Valid g) (h_nodup_N1 : N1.Nodup)
    (x : Fin n) (hxw : x ≠ w) :
    (toSimpleGraph (AdjMat.split_vertex g w N1 N2)).Adj
        (Fin.castSucc w) (Fin.castSucc x) ↔
      x ∈ N1 := by
  sorry

lemma split_vertex_get_v2_N2 (g : AdjMat n) (w : Fin n) (N1 N2 : List (Fin n))
    (h_valid : Valid g) (h_nodup_N2 : N2.Nodup)
    (x : Fin n) (hxw : x ≠ w) :
    (toSimpleGraph (AdjMat.split_vertex g w N1 N2)).Adj
        (Fin.last n) (Fin.castSucc x) ↔
      x ∈ N2 := by
  sorry

-- ============================================================
-- 10. Method 3-b の正当性
-- ============================================================

theorem apply_method3b_sound (g : AdjMat n) (g' : AdjMat (n + 1))
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_method3b g →
    Claim4GraphEnum.Spec.Method3b_Rel (toSimpleGraph g) (toSimpleGraph g') := by
  intro h_gen
  simp only [AdjMat.apply_method3b, List.mem_flatMap, List.mem_map, List.mem_filter] at h_gen
  simp only [List.mem_finRange, true_and] at h_gen
  obtain ⟨w, h_deg_w, parts, h_parts, rfl⟩ := h_gen
  have hw_deg : (toSimpleGraph g).degree w = 4 := by
    have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
    have hdeg := degree_correct g w h_valid.1 h_irref
    rw [beq_iff_eq, hdeg, ← SimpleGraph.degree] at h_deg_w
    exact h_deg_w
  simp only [AdjMat.partitions_of_4] at h_parts
  have h_len : (g.neighbors w).length = 4 := by
    rw [← degree_eq_neighbors_length]
    rw [beq_iff_eq] at h_deg_w
    exact h_deg_w
  have hw_deg_classic : @SimpleGraph.degree (Fin n) (toSimpleGraph g) w
      (@SimpleGraph.neighborSetFintype (Fin n) (toSimpleGraph g) (Fin.fintype n)
        (fun a b ↦ Classical.propDecidable ((toSimpleGraph g).Adj a b)) w) = 4 := by
    have h_nf_eq : @SimpleGraph.neighborFinset (Fin n) (toSimpleGraph g) w
          (@SimpleGraph.neighborSetFintype (Fin n) (toSimpleGraph g) (Fin.fintype n)
            (fun a b ↦ Classical.propDecidable ((toSimpleGraph g).Adj a b)) w) =
        (toSimpleGraph g).neighborFinset w := by
      ext x; simp [SimpleGraph.mem_neighborFinset]
    simp only [SimpleGraph.degree, h_nf_eq]
    exact hw_deg
  rcases hn : g.neighbors w with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · rw [hn] at h_len; simp only [List.length] at h_len; contradiction
  · rw [hn] at h_len; simp only [List.length] at h_len; contradiction
  · rw [hn] at h_len; simp only [List.length] at h_len; contradiction
  · rw [hn] at h_len; simp only [List.length] at h_len; contradiction
  · have h_tail : tail.length = 0 := by
      rw [hn] at h_len
      simp only [List.length_cons] at h_len
      omega
    have h_tail_nil : tail = [] := List.eq_nil_of_length_eq_zero h_tail
    have hn_eq : g.neighbors w = [a, b, c, d] := by
      rw [hn, h_tail_nil]
    rw [hn_eq] at h_parts
    simp only [List.mem_cons] at h_parts
    -- Get distinctness of a b c d from nodup of neighbors list
    have h_nodup : List.Nodup (g.neighbors w) := neighbors_nodup g w
    rw [hn_eq] at h_nodup
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := nodup_four_distinct h_nodup
    -- Get that a b c d are all in neighborFinset w
    have h_nfset : (toSimpleGraph g).neighborFinset w = {a, b, c, d} := by
      ext x; simp [neighborFinset_eq_of_valid g w h_valid.1 h_valid.2, hn_eq,
        Finset.mem_insert, Finset.mem_singleton]
    -- Helper: x ∈ neighbors w → x ≠ w (because g.get w w = false)
    have ne_of_neigh : ∀ x, x ∈ g.neighbors w → x ≠ w := by
      intro x hx heq
      cases heq
      have heq_true : g.get w w = true := (mem_neighbors_iff g w w).mp hx
      have heq_false : g.get w w = false := h_valid.2 w
      rw [heq_false] at heq_true
      contradiction
    have haw : a ≠ w := ne_of_neigh a (hn_eq ▸ List.mem_cons.mpr (Or.inl rfl))
    have hbw : b ≠ w := ne_of_neigh b (hn_eq ▸ List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
    have hcw : c ≠ w := ne_of_neigh c (hn_eq ▸ List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))
    have hdw : d ≠ w := ne_of_neigh d (hn_eq ▸ List.mem_cons.mpr (Or.inr
      (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))))))
    rcases h_parts with h_parts_list | h_parts_list | h_parts_list | h_parts_list | h_parts_list | h_parts_list | h_parts_list
    · -- case: parts = ([a,b], [c,d])
      have h_eq : parts = ([a, b], [c, d]) := h_parts_list
      subst h_eq
      have h_N1N2_part : ({a, b} : Finset (Fin n)) ∪ {c, d} = (toSimpleGraph g).neighborFinset w := by
        rw [h_nfset]; ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
      have h_N1N2_disj : Disjoint ({a, b} : Finset (Fin n)) {c, d} := by
        simp [Finset.disjoint_left, hac, had, hbc, hbd]
      let cfg : Claim4GraphEnum.Spec.SplitConfig n (toSimpleGraph g) := {
        w := w
        hw_deg := hw_deg_classic
        N1 := {a, b}
        N2 := {c, d}
        h_partition := by convert h_N1N2_part
        h_disjoint := h_N1N2_disj
        h_card1 := by simp [Finset.card_pair hab]
        h_card2 := by simp [Finset.card_pair hcd]
      }
      use cfg
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y hxw hyw
        exact split_vertex_get_old g w [a, b] [c, d] h_valid
          (by simp only [List.mem_cons]; rintro z (rfl | rfl | hc)
              · exact haw
              · exact hbw
              · cases hc)
          (by simp only [List.mem_cons]; rintro z (rfl | rfl | hc)
              · exact hcw
              · exact hdw
              · cases hc)
          x y hxw hyw
      · intro x hxw
        rw [split_vertex_get_v1_N1 g w [a, b] [c, d] h_valid (by simp [hab]) x hxw]
        simp [cfg]
      · intro x hxw
        rw [split_vertex_get_v2_N2 g w [a, b] [c, d] h_valid (by simp [hcd]) x hxw]
        simp [cfg]
      · exact split_vertex_adj_v1_v2 g w [a, b] [c, d] h_valid
    · -- case: parts = ([a,c], [b,d])
      have h_eq : parts = ([a, c], [b, d]) := h_parts_list
      subst h_eq
      have h_N1N2_part : ({a, c} : Finset (Fin n)) ∪ {b, d} = (toSimpleGraph g).neighborFinset w := by
        rw [h_nfset]; ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
      have h_N1N2_disj : Disjoint ({a, c} : Finset (Fin n)) {b, d} := by
        simp [Finset.disjoint_left, hab, hab.symm, hac, hac.symm, had, had.symm, hbc, hbc.symm, hbd, hbd.symm, hcd, hcd.symm]
      let cfg : Claim4GraphEnum.Spec.SplitConfig n (toSimpleGraph g) := {
        w := w
        hw_deg := hw_deg_classic
        N1 := {a, c}
        N2 := {b, d}
        h_partition := by convert h_N1N2_part
        h_disjoint := h_N1N2_disj
        h_card1 := by simp [Finset.card_pair hac]
        h_card2 := by simp [Finset.card_pair hbd]
      }
      use cfg
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y hxw hyw
        exact split_vertex_get_old g w [a, c] [b, d] h_valid
          (by simp only [List.mem_cons, List.mem_singleton]; rintro z (rfl | rfl | hc)
              · exact haw
              · exact hcw
              · cases hc)
          (by simp only [List.mem_cons, List.mem_singleton]; rintro z (rfl | rfl | hc)
              · exact hbw
              · exact hdw
              · cases hc)
          x y hxw hyw
      · intro x hxw
        rw [split_vertex_get_v1_N1 g w [a, c] [b, d] h_valid (by simp [hac]) x hxw]
        simp [cfg]
      · intro x hxw
        rw [split_vertex_get_v2_N2 g w [a, c] [b, d] h_valid (by simp [hbd]) x hxw]
        simp [cfg]
      · exact split_vertex_adj_v1_v2 g w [a, c] [b, d] h_valid
    · -- case: parts = ([a,d], [b,c])
      have h_eq : parts = ([a, d], [b, c]) := h_parts_list
      subst h_eq
      have h_N1N2_part : ({a, d} : Finset (Fin n)) ∪ {b, c} = (toSimpleGraph g).neighborFinset w := by
        rw [h_nfset]; ext x; simp [Finset.mem_insert, Finset.mem_singleton]; tauto
      have h_N1N2_disj : Disjoint ({a, d} : Finset (Fin n)) {b, c} := by
        simp [Finset.disjoint_left, hab, hac, hbd.symm, hcd.symm]
      let cfg : Claim4GraphEnum.Spec.SplitConfig n (toSimpleGraph g) := {
        w := w
        hw_deg := hw_deg_classic
        N1 := {a, d}
        N2 := {b, c}
        h_partition := by convert h_N1N2_part
        h_disjoint := h_N1N2_disj
        h_card1 := by simp [Finset.card_pair had]
        h_card2 := by simp [Finset.card_pair hbc]
      }
      use cfg
      simp only []
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro x y hxw hyw
        exact split_vertex_get_old g w [a, d] [b, c] h_valid
          (by simp only [List.mem_cons]; rintro z (rfl | rfl | hc)
              · exact haw
              · exact hdw
              · cases hc)
          (by simp only [List.mem_cons]; rintro z (rfl | rfl | hc)
              · exact hbw
              · exact hcw
              · cases hc)
          x y hxw hyw
      · intro x hxw
        rw [split_vertex_get_v1_N1 g w [a, d] [b, c] h_valid (by simp [had]) x hxw]
        simp [cfg]
      · intro x hxw
        rw [split_vertex_get_v2_N2 g w [a, d] [b, c] h_valid (by simp [hbc]) x hxw]
        simp [cfg]
      · exact split_vertex_adj_v1_v2 g w [a, d] [b, c] h_valid

lemma partitions_of_4_length {α : Type} [DecidableEq α] {ns : List α} {L1 L2 : List α}
    (h : (L1, L2) ∈ AdjMat.partitions_of_4 ns) : L1.length = 2 ∧ L2.length = 2 := by
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · contradiction
  · contradiction
  · contradiction
  · contradiction
  · revert h
    simp [AdjMat.partitions_of_4]
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · subst h1 h2; simp
    · subst h1 h2; simp
    · subst h1 h2; simp
    · subst h1 h2; simp
    · subst h1 h2; simp
    · subst h1 h2; simp

lemma exists_partition {α : Type} [DecidableEq α] (ns : List α)
    (h_len : ns.length = 4) (h_nodup : ns.Nodup)
    (N1 N2 : Finset α)
    (h_c1 : N1.card = 2) (h_c2 : N2.card = 2)
    (h_union : N1 ∪ N2 = ns.toFinset) :
    ∃ (L1 L2 : List α), (L1, L2) ∈ AdjMat.partitions_of_4 ns ∧ L1.toFinset = N1 ∧ L2.toFinset = N2 := by
  rcases ns with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, tail⟩⟩⟩⟩
  · simp at h_len
  · simp at h_len
  · simp at h_len
  · simp at h_len
  · have h_tail : tail = [] := by
      revert h_len; simp
    subst h_tail
    have h_nodup_abcd : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
      simp only [List.nodup_cons, List.mem_cons, not_or] at h_nodup
      tauto
    obtain ⟨hab, hac, had, hbc, hbd, hcd⟩ := h_nodup_abcd
    have h_sf : [a, b, c, d].toFinset = {a, b, c, d} := by
      ext e; simp
    rw [h_sf] at h_union

    -- local tactic to close subset equivalence
    have close_subsets : ∀ (x y z w : α)
      (hx : x ∈ N1) (hy : y ∈ N1) (hxy : x ≠ y) (hzw : z ≠ w)
      (hzx : z ≠ x) (hzy : z ≠ y) (hwx : w ≠ x) (hwy : w ≠ y)
      (h_eq_all : {x, y, z, w} = ({a, b, c, d} : Finset α)),
      ([x, y].toFinset = N1) ∧ ([z, w].toFinset = N2) := by
      intro x y z w hx hy hxy hzw hzx hzy hwx hwy h_eq_all
      have h_xy_card : ({x, y} : Finset α).card = 2 := by
        rw [Finset.card_pair hxy]
      have h1_sub : ({x, y} : Finset α) ⊆ N1 := by
        intro e he
        simp only [Finset.mem_insert, Finset.mem_singleton] at he
        rcases he with (rfl | rfl)
        · exact hx
        · exact hy
      have h1_eq : ({x, y} : Finset α) = N1 := by
        apply Finset.eq_of_subset_of_card_le h1_sub
        rw [h_xy_card, h_c1]
      have h1 : ([x, y] : List α).toFinset = N1 := by
        have h_list_eq : ([x, y] : List α).toFinset = {x, y} := by
          ext e
          simp
        rw [h_list_eq]
        exact h1_eq
      constructor
      · exact h1
      · have h_zw_card : ({z, w} : Finset α).card = 2 := by
          rw [Finset.card_pair hzw]
        have h2_sub : ({z, w} : Finset α) ⊆ N2 := by
          intro e he
          simp only [Finset.mem_insert, Finset.mem_singleton] at he
          have he_union : e ∈ N1 ∪ N2 := by
            rw [h_union, ← h_eq_all]
            simp only [Finset.mem_insert, Finset.mem_singleton]
            rcases he with (rfl | rfl)
            · right; right; left; rfl
            · right; right; right; rfl
          rw [Finset.mem_union] at he_union
          rcases he_union with he1 | he2
          · rw [← h1_eq] at he1
            simp only [Finset.mem_insert, Finset.mem_singleton] at he1
            rcases he with rfl | rfl
            · rcases he1 with rfl | rfl
              · exact False.elim (hzx rfl)
              · exact False.elim (hzy rfl)
            · rcases he1 with rfl | rfl
              · exact False.elim (hwx rfl)
              · exact False.elim (hwy rfl)
          · exact he2
        have h2_eq : ({z, w} : Finset α) = N2 := by
          apply Finset.eq_of_subset_of_card_le h2_sub
          rw [h_zw_card, h_c2]
        have h_list_eq2 : ([z, w] : List α).toFinset = {z, w} := by
          ext e
          simp
        rw [h_list_eq2]
        exact h2_eq


    by_cases ha : a ∈ N1
    · by_cases hb : b ∈ N1
      · use [a, b], [c, d]
        constructor
        · simp [AdjMat.partitions_of_4]
        · exact close_subsets a b c d ha hb hab hcd hac.symm hbc.symm had.symm hbd.symm (by ext e; simp; try tauto)
      · by_cases hc : c ∈ N1
        · use [a, c], [b, d]
          constructor
          · simp [AdjMat.partitions_of_4]
          · exact close_subsets a c b d ha hc hac hbd hab.symm hbc had.symm hcd.symm (by ext e; simp; tauto)
        · -- a ∈ N1, b ∉ N1, c ∉ N1. This implies d ∈ N1.
          have hd : d ∈ N1 := by
            by_contra hdn
            have h_sub : N1 ⊆ {a} := by
              intro e he
              have he2 : e ∈ ({a,b,c,d} : Finset α) := by
                rw [← h_union]; apply Finset.subset_union_left; exact he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he2
              rcases he2 with rfl | rfl | rfl | rfl
              · simp only [Finset.mem_singleton]
              · exact False.elim (hb he)
              · exact False.elim (hc he)
              · exact False.elim (hdn he)
            have h_le : N1.card ≤ 1 := by
              have h_card1 : ({a} : Finset α).card = 1 := Finset.card_singleton a
              rw [← h_card1]
              apply Finset.card_le_card h_sub
            rw [h_c1] at h_le
            omega
          use [a, d], [b, c]
          constructor
          · simp [AdjMat.partitions_of_4]
          · exact close_subsets a d b c ha hd had hbc hab.symm hbd hac.symm hcd (by ext e; simp; tauto)
    · -- a ∉ N1
      by_cases hb : b ∈ N1
      · by_cases hc : c ∈ N1
        · use [b, c], [a, d]
          constructor
          · simp [AdjMat.partitions_of_4]
          · exact close_subsets b c a d hb hc hbc had hab hac hbd.symm hcd.symm (by ext e; simp; tauto)
        · -- a ∉ N1, b ∈ N1, c ∉ N1. This implies d ∈ N1.
          have hd : d ∈ N1 := by
            by_contra hdn
            have h_sub : N1 ⊆ {b} := by
              intro e he
              have he2 : e ∈ ({a,b,c,d} : Finset α) := by
                rw [← h_union]; apply Finset.subset_union_left; exact he
              simp only [Finset.mem_insert, Finset.mem_singleton] at he2
              rcases he2 with rfl | rfl | rfl | rfl
              · exact False.elim (ha he)
              · simp only [Finset.mem_singleton]
              · exact False.elim (hc he)
              · exact False.elim (hdn he)
            have h_le : N1.card ≤ 1 := by
              have h_card1 : ({b} : Finset α).card = 1 := Finset.card_singleton b
              rw [← h_card1]
              apply Finset.card_le_card h_sub
            rw [h_c1] at h_le
            omega
          use [b, d], [a, c]
          constructor
          · simp [AdjMat.partitions_of_4]
          · exact close_subsets b d a c hb hd hbd hac hab had hbc.symm hcd (by ext e; simp; tauto)
      · -- a ∉ N1, b ∉ N1. This implies c ∈ N1 and d ∈ N1.
        have hc : c ∈ N1 := by
          by_contra hcn
          have h_sub : N1 ⊆ {d} := by
            intro e he
            have he2 : e ∈ ({a,b,c,d} : Finset α) := by
              rw [← h_union]; apply Finset.subset_union_left; exact he
            simp only [Finset.mem_insert, Finset.mem_singleton] at he2
            rcases he2 with rfl | rfl | rfl | rfl
            · exact False.elim (ha he)
            · exact False.elim (hb he)
            · exact False.elim (hcn he)
            · simp only [Finset.mem_singleton]
          have h_le : N1.card ≤ 1 := by
            have h_card1 : ({d} : Finset α).card = 1 := Finset.card_singleton d
            rw [← h_card1]
            apply Finset.card_le_card h_sub
          rw [h_c1] at h_le
          omega
        have hd : d ∈ N1 := by
          by_contra hdn
          have h_sub : N1 ⊆ {c} := by
            intro e he
            have he2 : e ∈ ({a,b,c,d} : Finset α) := by
              rw [← h_union]; apply Finset.subset_union_left; exact he
            simp only [Finset.mem_insert, Finset.mem_singleton] at he2
            rcases he2 with rfl | rfl | rfl | rfl
            · exact False.elim (ha he)
            · exact False.elim (hb he)
            · simp only [Finset.mem_singleton]
            · exact False.elim (hdn he)
          have h_le : N1.card ≤ 1 := by
            have h_card1 : ({c} : Finset α).card = 1 := Finset.card_singleton c
            rw [← h_card1]
            apply Finset.card_le_card h_sub
          rw [h_c1] at h_le
          omega
        use [c, d], [a, b]
        constructor
        · simp [AdjMat.partitions_of_4]
        · exact close_subsets c d a b hc hd hcd hab hac had hbc hbd (by ext e; simp; tauto)

lemma method3b_rel_unique (G : SimpleGraph (Fin n)) (G1 G2 : SimpleGraph (Fin (n + 1)))
    (cfg : Claim4GraphEnum.Spec.SplitConfig n G)
    (h1 : let v1 := Fin.castSucc cfg.w; let v2 := Fin.last n
          (∀ x y, x ≠ cfg.w → y ≠ cfg.w → (G1.Adj (Fin.castSucc x) (Fin.castSucc y) ↔ G.Adj x y)) ∧
          (∀ x, x ≠ cfg.w → (G1.Adj v1 (Fin.castSucc x) ↔ x ∈ cfg.N1)) ∧
          (∀ x, x ≠ cfg.w → (G1.Adj v2 (Fin.castSucc x) ↔ x ∈ cfg.N2)) ∧
          G1.Adj v1 v2)
    (h2 : let v1 := Fin.castSucc cfg.w; let v2 := Fin.last n
          (∀ x y, x ≠ cfg.w → y ≠ cfg.w → (G2.Adj (Fin.castSucc x) (Fin.castSucc y) ↔ G.Adj x y)) ∧
          (∀ x, x ≠ cfg.w → (G2.Adj v1 (Fin.castSucc x) ↔ x ∈ cfg.N1)) ∧
          (∀ x, x ≠ cfg.w → (G2.Adj v2 (Fin.castSucc x) ↔ x ∈ cfg.N2)) ∧
          G2.Adj v1 v2) :
    G1 = G2 := by
  rcases h1 with ⟨h1_old, h1_v1, h1_v2, h1_v1v2⟩
  rcases h2 with ⟨h2_old, h2_v1, h2_v2, h2_v1v2⟩
  ext u v
  cases u using Fin.lastCases
  · cases v using Fin.lastCases
    · simp
    · rename_i y
      by_cases hyw : y = cfg.w
      · subst hyw
        have s1 : G1.Adj (Fin.last n) (Fin.castSucc cfg.w) ↔ G1.Adj (Fin.castSucc cfg.w) (Fin.last n) :=
          ⟨fun h => G1.symm h, fun h => G1.symm h⟩
        have s2 : G2.Adj (Fin.last n) (Fin.castSucc cfg.w) ↔ G2.Adj (Fin.castSucc cfg.w) (Fin.last n) :=
          ⟨fun h => G2.symm h, fun h => G2.symm h⟩
        rw [s1, s2]
        exact iff_of_true h1_v1v2 h2_v1v2
      · have s1 : G1.Adj (Fin.last n) (Fin.castSucc y) ↔ G1.Adj (Fin.castSucc y) (Fin.last n) :=
          ⟨fun h => G1.symm h, fun h => G1.symm h⟩
        have s2 : G2.Adj (Fin.last n) (Fin.castSucc y) ↔ G2.Adj (Fin.castSucc y) (Fin.last n) :=
          ⟨fun h => G2.symm h, fun h => G2.symm h⟩
        -- we actually want G1.Adj (last n) (cast y) to rewrite with h1_v2!
        -- so we just directly rw [h1_v2 y hyw, h2_v2 y hyw]!
        rw [h1_v2 y hyw, h2_v2 y hyw]
  · rename_i x
    cases v using Fin.lastCases
    · by_cases hxw : x = cfg.w
      · subst hxw
        exact iff_of_true h1_v1v2 h2_v1v2
      · have s1 : G1.Adj (Fin.castSucc x) (Fin.last n) ↔ G1.Adj (Fin.last n) (Fin.castSucc x) :=
          ⟨fun h => G1.symm h, fun h => G1.symm h⟩
        have s2 : G2.Adj (Fin.castSucc x) (Fin.last n) ↔ G2.Adj (Fin.last n) (Fin.castSucc x) :=
          ⟨fun h => G2.symm h, fun h => G2.symm h⟩
        rw [s1, s2]
        rw [h1_v2 x hxw, h2_v2 x hxw]
    · rename_i y
      by_cases hxw : x = cfg.w
      · subst hxw
        by_cases hyw : y = cfg.w
        · subst hyw; simp
        · rw [h1_v1 y hyw, h2_v1 y hyw]
      · by_cases hyw : y = cfg.w
        · subst hyw
          have s1 : G1.Adj (Fin.castSucc x) (Fin.castSucc cfg.w) ↔ G1.Adj (Fin.castSucc cfg.w) (Fin.castSucc x) :=
            ⟨fun h => G1.symm h, fun h => G1.symm h⟩
          have s2 : G2.Adj (Fin.castSucc x) (Fin.castSucc cfg.w) ↔ G2.Adj (Fin.castSucc cfg.w) (Fin.castSucc x) :=
            ⟨fun h => G2.symm h, fun h => G2.symm h⟩
          rw [s1, s2]
          rw [h1_v1 x hxw, h2_v1 x hxw]
        · rw [h1_old x y hxw hyw, h2_old x y hxw hyw]

theorem apply_method3b_complete (g : AdjMat n) (G' : SimpleGraph (Fin (n + 1)))
    (h_valid : Valid g) (h_G : Claim4GraphEnum.Spec.Method3b_Rel (toSimpleGraph g) G') :
    ∃ g' ∈ AdjMat.apply_method3b g, toSimpleGraph g' = G' := by
  rcases h_G with ⟨cfg, h_old', h_v1', h_v2', h_v1v2'⟩
  have hw_deg := cfg.hw_deg
  have h_part : cfg.N1 ∪ cfg.N2 = (g.neighbors cfg.w).toFinset := by
    rw [neighbors_correct g cfg.w h_valid.1 h_valid.2]
    convert cfg.h_partition
  have h_len : (g.neighbors cfg.w).length = 4 := by
    rw [← degree_eq_neighbors_length]
    rw [degree_correct g cfg.w h_valid.1 h_valid.2]
    rw [← SimpleGraph.degree]
    convert hw_deg
  have h_nodup : (g.neighbors cfg.w).Nodup := neighbors_nodup g cfg.w
  obtain ⟨L1, L2, h_part4, h_L1, h_L2⟩ := exists_partition (g.neighbors cfg.w) h_len h_nodup cfg.N1 cfg.N2 cfg.h_card1 cfg.h_card2 h_part
  let g' := AdjMat.split_vertex g cfg.w L1 L2
  use g'
  constructor
  · -- prove g' ∈ apply_method3b g
    simp only [AdjMat.apply_method3b, List.mem_flatMap, List.mem_filter, List.mem_finRange,
    beq_iff_eq, true_and, List.mem_map, Prod.exists]
    use cfg.w
    constructor
    · simp only [degree_correct g cfg.w h_valid.1 h_valid.2,
        card_neighborFinset_eq_degree]
      convert hw_deg
    · use L1, L2
  · -- prove toSimpleGraph g' = G'
    -- we extract the 4 properties of G' from h_G
    have h_lens := partitions_of_4_length h_part4
    have h_L1_nodup : L1.Nodup := by
      rw [← List.dedup_eq_self]
      have h_dedup_len : L1.dedup.length = L1.length := by
        have h1 : L1.toFinset.card = L1.length := by
          rw [h_L1, cfg.h_card1, h_lens.1]
        rwa [List.card_toFinset] at h1
      exact (List.dedup_sublist L1).eq_of_length h_dedup_len
    have h_L2_nodup : L2.Nodup := by
      rw [← List.dedup_eq_self]
      have h_dedup_len : L2.dedup.length = L2.length := by
        have h1 : L2.toFinset.card = L2.length := by
          rw [h_L2, cfg.h_card2, h_lens.2]
        rwa [List.card_toFinset] at h1
      exact (List.dedup_sublist L2).eq_of_length h_dedup_len
    have h_L1_w : ∀ x ∈ L1, x ≠ cfg.w := by
      intro x hx
      have hx2 : x ∈ cfg.N1 := h_L1 ▸ (List.mem_toFinset.mpr hx)
      have hx3 : x ∈ (toSimpleGraph g).neighborFinset cfg.w := by
        convert (Finset.ext_iff.1 cfg.h_partition x).1 (Finset.mem_union_left cfg.N2 hx2)
      intro heq; subst heq
      -- ここから修正
      have h_adj : (toSimpleGraph g).Adj cfg.w cfg.w := (SimpleGraph.mem_neighborFinset (toSimpleGraph g) cfg.w cfg.w).mp hx3
      exact h_adj.ne rfl
    have h_L2_w : ∀ x ∈ L2, x ≠ cfg.w := by
      intro x hx
      have hx2 : x ∈ cfg.N2 := h_L2 ▸ (List.mem_toFinset.mpr hx)
      have hx3 : x ∈ (toSimpleGraph g).neighborFinset cfg.w := by
        convert (Finset.ext_iff.1 cfg.h_partition x).1 (Finset.mem_union_right cfg.N1 hx2)
      intro heq; subst heq
      have h_adj : (toSimpleGraph g).Adj cfg.w cfg.w := (SimpleGraph.mem_neighborFinset (toSimpleGraph g) cfg.w cfg.w).mp hx3
      exact h_adj.ne rfl
    apply method3b_rel_unique (toSimpleGraph g) (toSimpleGraph g') G' cfg
    · constructor
      · intro x y hx hy
        exact split_vertex_get_old g cfg.w L1 L2 h_valid h_L1_w h_L2_w x y hx hy
      · constructor
        · intro x hx
          have hrw := split_vertex_get_v1_N1 g cfg.w L1 L2 h_valid h_L1_nodup x hx
          -- hrw is x ∈ L1, we need x ∈ cfg.N1
          rw [hrw]
          exact List.mem_toFinset.symm.trans (by rw [h_L1])
        · constructor
          · intro x hx
            have hrw := split_vertex_get_v2_N2 g cfg.w L1 L2 h_valid h_L2_nodup x hx
            rw [hrw]
            exact List.mem_toFinset.symm.trans (by rw [h_L2])
          · exact split_vertex_adj_v1_v2 g cfg.w L1 L2 h_valid
    · exact ⟨h_old', h_v1', h_v2', h_v1v2'⟩

-- ============================================================
-- 11. Method 1 の正当性
-- ============================================================

lemma get_foldl_add_edge_map {n m : ℕ} {α : Type} (tgt : AdjMat m) (l : List α) (f : α → Fin m × Fin m) (u v : Fin m) :
  (List.foldl (fun acc x => acc.add_edge (f x).1 (f x).2) tgt l).get u v = true ↔
  (tgt.get u v = true ∨ ∃ x ∈ l, f x = (u, v) ∨ f x = (v, u)) := by
  induction l generalizing tgt with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih]
    rw [AdjMat.get_add_edge]
    simp only [Bool.or_eq_true, decide_eq_true_iff, List.mem_cons]
    have h1 : u = (f hd).1 ∧ v = (f hd).2 ↔ f hd = (u, v) := by
      calc
        u = (f hd).1 ∧ v = (f hd).2 ↔ (u, v) = f hd := ⟨fun ⟨h1, h2⟩ => by rw [h1, h2], fun h => by rw [← h]; exact ⟨rfl, rfl⟩⟩
        _ ↔ f hd = (u, v) := eq_comm
    have h2 : u = (f hd).2 ∧ v = (f hd).1 ↔ f hd = (v, u) := by
      calc
        u = (f hd).2 ∧ v = (f hd).1 ↔ (v, u) = f hd := ⟨fun ⟨h1, h2⟩ => by rw [h1, h2], fun h => by rw [← h]; exact ⟨rfl, rfl⟩⟩
        _ ↔ f hd = (v, u) := eq_comm
    rw [h1, h2]
    tauto

lemma method1_rel_unique (n : ℕ) (g : AdjMat n) (v1 v2 x1a x1b x2a x2b : Fin n)
    (h_valid : Valid g) (g' : AdjMat (n+2))
    (h_g' : g' = ((((List.foldl (fun acc x => acc.add_edge x.1 x.2)
                            (List.foldl (fun acc x => acc.add_edge (Fin.castAdd 2 x.1) (Fin.castAdd 2 x.2))
                              (AdjMat.empty (n + 2))
                              (List.flatMap
                                (fun i =>
                                  List.filterMap
                                    (fun j =>
                                      if
                                          (decide (↑i < ↑j) && decide (i ≠ v1) && decide (i ≠ v2) &&
                                                  decide (j ≠ v1) &&
                                                decide (j ≠ v2) &&
                                              g.get i j) =
                                            true then
                                        some (i, j)
                                      else none)
                                    (List.finRange n))
                                (List.finRange n)))
                            (List.flatMap
                              (fun i =>
                                List.filterMap (fun j => if ↑i < ↑j then some (i, j) else none)
                                  [Fin.castAdd 2 v1, Fin.castAdd 2 v2, ⟨n, by omega⟩, ⟨n + 1, by omega⟩])
                              [Fin.castAdd 2 v1, Fin.castAdd 2 v2, ⟨n, by omega⟩, ⟨n + 1, by omega⟩])).add_edge
                        (Fin.castAdd 2 v1) (Fin.castAdd 2 x1a)).add_edge
                    ⟨n, by omega⟩ (Fin.castAdd 2 x1b)).add_edge
                (Fin.castAdd 2 v2) (Fin.castAdd 2 x2a)).add_edge
            ⟨n + 1, by omega⟩ (Fin.castAdd 2 x2b))
    (cfg : Claim4GraphEnum.Spec.Method1Config n (toSimpleGraph g))
    (h_cfg_v1 : cfg.v1 = v1) (h_cfg_v2 : cfg.v2 = v2)
    (h_cfg_x1a : cfg.x1a = x1a) (h_cfg_x1b : cfg.x1b = x1b)
    (h_cfg_x2a : cfg.x2a = x2a) (h_cfg_x2b : cfg.x2b = x2b) :
    Claim4GraphEnum.Spec.Method1_Rel (toSimpleGraph g) (toSimpleGraph g') := by
  use cfg
  subst h_g'
  subst h_cfg_v1 h_cfg_v2 h_cfg_x1a h_cfg_x1b h_cfg_x2a h_cfg_x2b

  -- Unfold the g' graph node connections into direct propositional equalities
  have h_g'get : ∀ u w : Fin (n + 2),
    (((((List.foldl (fun acc x => acc.add_edge x.1 x.2)
                            (List.foldl (fun acc x => acc.add_edge (Fin.castAdd 2 x.1) (Fin.castAdd 2 x.2))
                              (AdjMat.empty (n + 2))
                              (List.flatMap
                                (fun i =>
                                  List.filterMap
                                    (fun j =>
                                      if
                                          (decide (↑i < ↑j) && decide (i ≠ cfg.v1) && decide (i ≠ cfg.v2) &&
                                                  decide (j ≠ cfg.v1) &&
                                                decide (j ≠ cfg.v2) &&
                                              g.get i j) =
                                            true then
                                        some (i, j)
                                      else none)
                                    (List.finRange n))
                                (List.finRange n)))
                            (List.flatMap
                              (fun i =>
                                List.filterMap (fun j => if ↑i < ↑j then some (i, j) else none)
                                  [Fin.castAdd 2 cfg.v1, Fin.castAdd 2 cfg.v2, ⟨n, by omega⟩, ⟨n + 1, by omega⟩])
                              [Fin.castAdd 2 cfg.v1, Fin.castAdd 2 cfg.v2, ⟨n, by omega⟩, ⟨n + 1, by omega⟩])).add_edge
                        (Fin.castAdd 2 cfg.v1) (Fin.castAdd 2 cfg.x1a)).add_edge
                    ⟨n, by omega⟩ (Fin.castAdd 2 cfg.x1b)).add_edge
                (Fin.castAdd 2 cfg.v2) (Fin.castAdd 2 cfg.x2a)).add_edge
            ⟨n + 1, by omega⟩ (Fin.castAdd 2 cfg.x2b)).get u w = true ↔
      (u = Fin.castAdd 2 cfg.v1 ∧ w = Fin.castAdd 2 cfg.x1a ∨ u = Fin.castAdd 2 cfg.x1a ∧ w = Fin.castAdd 2 cfg.v1) ∨
      (u = ⟨n, by omega⟩ ∧ w = Fin.castAdd 2 cfg.x1b ∨ u = Fin.castAdd 2 cfg.x1b ∧ w = ⟨n, by omega⟩) ∨
      (u = Fin.castAdd 2 cfg.v2 ∧ w = Fin.castAdd 2 cfg.x2a ∨ u = Fin.castAdd 2 cfg.x2a ∧ w = Fin.castAdd 2 cfg.v2) ∨
      (u = ⟨n + 1, by omega⟩ ∧ w = Fin.castAdd 2 cfg.x2b ∨ u = Fin.castAdd 2 cfg.x2b ∧ w = ⟨n + 1, by omega⟩) ∨
      (∃ x y : Fin (n + 2), x ∈ [Fin.castAdd 2 cfg.v1, Fin.castAdd 2 cfg.v2, (⟨n, by omega⟩ : Fin (n + 2)), ⟨n + 1, by omega⟩] ∧
        y ∈ [Fin.castAdd 2 cfg.v1, Fin.castAdd 2 cfg.v2, (⟨n, by omega⟩ : Fin (n + 2)), ⟨n + 1, by omega⟩] ∧ x.val < y.val ∧
        (u = x ∧ w = y ∨ u = y ∧ w = x)) ∨
      (∃ i j : Fin n, i.val < j.val ∧ i ≠ cfg.v1 ∧ i ≠ cfg.v2 ∧ j ≠ cfg.v1 ∧ j ≠ cfg.v2 ∧ g.get i j = true ∧
        (u = Fin.castAdd 2 i ∧ w = Fin.castAdd 2 j ∨ u = Fin.castAdd 2 j ∧ w = Fin.castAdd 2 i)) := by
    intro u w
    simp only [AdjMat.get_add_edge, Bool.or_eq_true, beq_iff_eq]
    simp only [get_foldl_add_edge_map, AdjMat.get_empty, Bool.false_eq_true, false_or, List.mem_flatMap, List.mem_filterMap, List.mem_finRange, true_and]
    -- Flatten out string of bool equivalences
    have h_symm : ∀ i j : Fin n, (g.get i j = true) ↔ (g.get j i = true) := by
      intro i j
      have h1 := h_valid.left i j
      rw [h1]
    tauto

  have u1 := Fin.castAdd 2 cfg.v1
  have u2 := Fin.castAdd 2 cfg.v2
  have u3 : Fin (n + 2) := ⟨n, by omega⟩
  have u4 : Fin (n + 2) := ⟨n + 1, by omega⟩
  have U : Finset (Fin (n + 2)) := {u1, u2, u3, u4}

  constructor
  · -- 1. Old nodes unchanged
    intro x y hx1 hx2 hy1 hy2
    rw [toSimpleGraph_adj, toSimpleGraph_adj]
    have h_get := h_g'get (Fin.castAdd 2 x) (Fin.castAdd 2 y)
    simp only [Fin.ext_iff] at hx1 hx2 hy1 hy2
    sorry
  · constructor
    · -- 2. K4 completeness
      intro x y hx hy hxy
      rw [toSimpleGraph_adj]
      have h_get := h_g'get x y
      -- Enumerate U combinations
      sorry
    · constructor
      · -- 3. u1 connections
        intro x hx1 hx2
        rw [toSimpleGraph_adj]
        have h_get := h_g'get u1 (Fin.castAdd 2 x)
        sorry
      · constructor
        · -- 4. u3 connections
          intro x hx1 hx2
          rw [toSimpleGraph_adj]
          have h_get := h_g'get u3 (Fin.castAdd 2 x)
          sorry
        · constructor
          · -- 5. u2 connections
            intro x hx1 hx2
            rw [toSimpleGraph_adj]
            have h_get := h_g'get u2 (Fin.castAdd 2 x)
            sorry
          · -- 6. u4 connections
            intro x hx1 hx2
            rw [toSimpleGraph_adj]
            have h_get := h_g'get u4 (Fin.castAdd 2 x)
            sorry

theorem apply_method1_sound (g : AdjMat n) (g' : AdjMat (n + 2))
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_method1 g →
    Claim4GraphEnum.Spec.Method1_Rel (toSimpleGraph g) (toSimpleGraph g') := by
  intro hmem
  simp only [AdjMat.apply_method1, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and, List.mem_filterMap] at hmem
  rcases hmem with ⟨⟨v1, v2⟩, ⟨u1, h_u1_deg, u2, h_u2_deg, h_edge_eq⟩, h_g'⟩
  revert h_edge_eq
  split_ifs with h_if
  · intro h_eq; injection h_eq with h_eq_pair
    injection h_eq_pair
    subst u1 u2
    have hv1_deg : g.degree v1 = 3 := by
      revert h_u1_deg; simp
    have hv2_deg : g.degree v2 = 3 := by
      revert h_u2_deg; simp
    have h_adj : g.get v1 v2 = true := by
      revert h_if; simp
    have h_v1_lt_v2 : v1.val < v2.val := by
      revert h_if; simp; tauto
    have h_v1v2_neq : v1 ≠ v2 := by
      intro h; subst h; omega

    revert h_g'
    rcases h_X1 : (g.neighbors v1).filter (fun x => x ≠ v2) with _ | ⟨x1a, _ | ⟨x1b, tail1⟩⟩
    · simp
    · simp
    · rcases h_X2 : (g.neighbors v2).filter (fun x => x ≠ v1) with _ | ⟨x2a, _ | ⟨x2b, tail2⟩⟩
      · simp
      · simp
      · cases tail1
        · cases tail2
          · intro h_g'
            simp at h_g'
            have h_adj2 : (toSimpleGraph g).Adj v1 v2 := by
              rw [toSimpleGraph_adj]
              exact ⟨Or.inl h_adj, h_v1v2_neq⟩
            have h_nodup_v1 : (g.neighbors v1).Nodup := Correctness.neighbors_nodup g v1
            have h_nodup_v2 : (g.neighbors v2).Nodup := Correctness.neighbors_nodup g v2
            have h_x1_nodup : [x1a, x1b].Nodup := by
              rw [← h_X1]
              exact List.Nodup.filter _ h_nodup_v1
            have h_x1_neq : x1a ≠ x1b := by
              simp only [List.nodup_cons, List.mem_singleton, not_false_eq_true] at h_x1_nodup
              exact h_x1_nodup.1
            have h_x2_nodup : [x2a, x2b].Nodup := by
              rw [← h_X2]
              exact List.Nodup.filter _ h_nodup_v2
            have h_x2_neq : x2a ≠ x2b := by
              simp only [List.nodup_cons, List.mem_singleton, not_false_eq_true] at h_x2_nodup
              exact h_x2_nodup.1

            have h_mem_n1 : ∀ x, x ∈ g.neighbors v1 ↔ g.get v1 x := by
              intro x; simp [AdjMat.neighbors]
            have h_mem_n2 : ∀ x, x ∈ g.neighbors v2 ↔ g.get v2 x := by
              intro x; simp [AdjMat.neighbors]

            have h_x1_eq : ({x1a, x1b} : Finset (Fin n)) = (toSimpleGraph g).neighborFinset v1 \ {v2} := by
              ext e
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
              have h_eq2 : e = x1a ∨ e = x1b ↔ e ∈ [x1a, x1b] := by simp
              rw [h_eq2, ← h_X1, List.mem_filter]
              rw [h_mem_n1]
              have h_symm : ∀ a b, g.get a b = g.get b a := h_valid.left
              constructor
              · intro ⟨h_get, h_neq⟩
                constructor
                · rw [toSimpleGraph_adj]
                  exact ⟨Or.inl h_get, by intro heq; subst heq; have hloop := h_valid.right v1; rw [hloop] at h_get; contradiction⟩
                · exact of_decide_eq_true h_neq
              · intro ⟨h_adj, h_neq⟩
                rw [toSimpleGraph_adj] at h_adj
                rcases h_adj.1 with h1 | h2
                · exact ⟨h1, decide_eq_true h_neq⟩
                · exact ⟨(h_symm e v1).symm ▸ h2, decide_eq_true h_neq⟩

            have h_x2_eq : ({x2a, x2b} : Finset (Fin n)) = (toSimpleGraph g).neighborFinset v2 \ {v1} := by
              ext e
              simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_sdiff, SimpleGraph.mem_neighborFinset]
              have h_eq2 : e = x2a ∨ e = x2b ↔ e ∈ [x2a, x2b] := by simp
              rw [h_eq2, ← h_X2, List.mem_filter]
              rw [h_mem_n2]
              have h_symm : ∀ a b, g.get a b = g.get b a := h_valid.left
              constructor
              · intro ⟨h_get, h_neq⟩
                constructor
                · rw [toSimpleGraph_adj]
                  exact ⟨Or.inl h_get, by intro heq; subst heq; have hloop := h_valid.right v2; rw [hloop] at h_get; contradiction⟩
                · exact of_decide_eq_true h_neq
              · intro ⟨h_adj, h_neq⟩
                rw [toSimpleGraph_adj] at h_adj
                rcases h_adj.1 with h1 | h2
                · exact ⟨h1, decide_eq_true h_neq⟩
                · exact ⟨(h_symm e v2).symm ▸ h2, decide_eq_true h_neq⟩

            rcases h_g' with rfl | rfl | rfl | rfl
            · sorry
            · sorry
            · sorry
            · sorry
          · simp
        · simp
  · intro h_eq; injection h_eq

theorem apply_method1_complete (g : AdjMat n) (G' : SimpleGraph (Fin (n + 2)))
    (h_valid : Valid g) :
    Claim4GraphEnum.Spec.Method1_Rel (toSimpleGraph g) G' →
    ∃ g' ∈ AdjMat.apply_method1 g, toSimpleGraph g' = G' := by
  rintro ⟨cfg, h_Rel⟩
  -- The configuration gives us two adjacent vertices v1, v2 with degree 3
  -- apply_method1 iterates over all valid pairs and configurations of their neighbors
  -- We just need to show that cfg.x1a, cfg.x1b, cfg.x2a, cfg.x2b corresponds to one of the pairs generated.
  sorry

-- ============================================================
-- 12. 逆操作の正当性
-- ============================================================

lemma toSimpleGraph_remove_edge (g : AdjMat n) (u v : Fin n) (x y : Fin n) :
    (toSimpleGraph (g.remove_edge u v)).Adj x y ↔
    (toSimpleGraph g).Adj x y ∧ ¬(x = u ∧ y = v) ∧ ¬(x = v ∧ y = u) := by
  simp only [toSimpleGraph_adj, AdjMat.remove_edge, AdjMat.get_set_eq]
  split_ifs <;> tauto

theorem apply_inv_method2_sound (g : AdjMat n) (g' : AdjMat n)
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_inv_method2 g →
    Claim4GraphEnum.Spec.Method2_Rel (toSimpleGraph g') (toSimpleGraph g) := by
  intro hmem
  simp only [AdjMat.apply_inv_method2, List.mem_map] at hmem
  obtain ⟨⟨u, v⟩, h_pair, rfl⟩ := hmem
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and] at h_pair
  obtain ⟨u', hu_deg, v', hv_deg, h_fmap⟩ := h_pair
  split_ifs at h_fmap with h_cond
  simp only [Option.some.injEq, Prod.mk.injEq] at h_fmap
  obtain ⟨rfl, rfl⟩ := h_fmap
  dsimp only at *
  simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
  have h_u_lt_v : u'.val < v'.val := h_cond.1
  have h_adj : g.get u' v' = true := h_cond.2
  have h_neq : u' ≠ v' := Fin.ne_of_lt h_u_lt_v
  have h_deg_u : g.degree u' = 4 := by
    have aux : (g.degree u' == 4) = true := hu_deg
    rw [beq_iff_eq] at aux; exact aux
  have h_deg_v : g.degree v' = 4 := by
    have aux : (g.degree v' == 4) = true := hv_deg
    rw [beq_iff_eq] at aux; exact aux
  use u', v', h_neq
  have h_irref : ∀ a : Fin n, g.get a a = false := h_valid.2
  have h_symm : ∀ a b : Fin n, g.get a b = g.get b a := h_valid.1
  have hg'_valid := valid_remove_edge h_valid (u := u') (v := v')
  have h_insert_u : (toSimpleGraph g).neighborFinset u' = insert v' ((toSimpleGraph (g.remove_edge u' v')).neighborFinset u') := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, toSimpleGraph_adj, Finset.mem_insert, AdjMat.remove_edge, AdjMat.get_set_eq]
    by_cases h1 : x = v'
    · rw [h1]
      have hc : u' = v' ↔ False := ⟨fun h => h_neq h, False.elim⟩
      have hc2 : v' = u' ↔ False := ⟨fun h => h_neq h.symm, False.elim⟩
      simp_all
    · have hc : u' = x ∧ v' = u' ↔ False := ⟨by rintro ⟨_, rfl⟩; exact h_neq rfl, False.elim⟩
      split_ifs <;> simp_all
  have h_insert_v : (toSimpleGraph g).neighborFinset v' = insert u' ((toSimpleGraph (g.remove_edge u' v')).neighborFinset v') := by
    ext x
    simp only [SimpleGraph.mem_neighborFinset, toSimpleGraph_adj, Finset.mem_insert, AdjMat.remove_edge, AdjMat.get_set_eq]
    by_cases h1 : x = u'
    · rw [h1]
      have hc : v' = u' ↔ False := ⟨fun h => h_neq h.symm, False.elim⟩
      have hc2 : u' = v' ↔ False := ⟨fun h => h_neq h, False.elim⟩
      have ha : g.get u' v' = true := h_adj
      rw [h_symm] at ha
      simp_all
    · have hc : v' = x ∧ u' = v' ↔ False := ⟨by rintro ⟨_, rfl⟩; exact h_neq rfl, False.elim⟩
      split_ifs <;> simp_all
  have hG'_not_adj : ¬(toSimpleGraph (g.remove_edge u' v')).Adj u' v' := by
    rw [adj_iff_get _ u' v' hg'_valid.1 hg'_valid.2]
    simp [AdjMat.remove_edge, AdjMat.get_set_eq]
  have hG_deg_u : (toSimpleGraph g).degree u' = (toSimpleGraph (g.remove_edge u' v')).degree u' + 1 := by
    have h1 : (toSimpleGraph g).degree u' = ((toSimpleGraph g).neighborFinset u').card := rfl
    have h2 : ((toSimpleGraph (g.remove_edge u' v')).neighborFinset u').card = (toSimpleGraph (g.remove_edge u' v')).degree u' := rfl
    rw [h1, h_insert_u, Finset.card_insert_of_notMem, h2]
    intro hc
    rw [SimpleGraph.mem_neighborFinset] at hc
    exact hG'_not_adj hc
  have hG_deg_v : (toSimpleGraph g).degree v' = (toSimpleGraph (g.remove_edge u' v')).degree v' + 1 := by
    have h1 : (toSimpleGraph g).degree v' = ((toSimpleGraph g).neighborFinset v').card := rfl
    have h2 : ((toSimpleGraph (g.remove_edge u' v')).neighborFinset v').card = (toSimpleGraph (g.remove_edge u' v')).degree v' := rfl
    rw [h1, h_insert_v, Finset.card_insert_of_notMem, h2]
    intro hc
    rw [SimpleGraph.mem_neighborFinset] at hc
    exact hG'_not_adj (SimpleGraph.Adj.symm hc)
  have hG_add : toSimpleGraph g = Claim4GraphEnum.Spec.add_edge (toSimpleGraph (g.remove_edge u' v')) u' v' h_neq := by
    ext x y
    simp only [Claim4GraphEnum.Spec.add_edge, toSimpleGraph_adj, AdjMat.remove_edge, AdjMat.get_set_eq]
    constructor
    · rintro ⟨h_get | h_get, h_xy⟩
      · by_cases h : x = u' ∧ y = v'
        · right; left; exact h
        · by_cases h2 : x = v' ∧ y = u'
          · right; right; exact h2
          · left; exact ⟨Or.inl (by split_ifs <;> tauto), h_xy⟩
      · by_cases h : y = u' ∧ x = v'
        · right; right; exact ⟨h.2, h.1⟩
        · by_cases h2 : y = v' ∧ x = u'
          · right; left; exact ⟨h2.2, h2.1⟩
          · left; exact ⟨Or.inr (by split_ifs <;> tauto), h_xy⟩
    · rintro (⟨h_get | h_get, h_xy⟩ | h_uv | h_vu)
      · revert h_get; split_ifs
        · intro hc; contradiction
        · intro hc; contradiction
        · intro hg; exact ⟨Or.inl hg, h_xy⟩
      · revert h_get; split_ifs
        · intro hc; contradiction
        · intro hc; contradiction
        · intro hg; exact ⟨Or.inr hg, h_xy⟩
      · exact ⟨Or.inl (by rw [h_uv.1, h_uv.2]; exact h_adj), (by rw [h_uv.1, h_uv.2]; exact h_neq)⟩
      · exact ⟨Or.inr (by rw [h_vu.1, h_vu.2]; exact h_adj), (by rw [h_vu.1, h_vu.2]; exact h_neq.symm)⟩
  constructor
  · -- G'.degree u' = 3
    have h_deg1 : (toSimpleGraph g).degree u' = 4 := by rw [SimpleGraph.degree, ← degree_correct g u' h_valid.1 h_valid.2]; exact h_deg_u
    have h_step : 4 = (toSimpleGraph (g.remove_edge u' v')).degree u' + 1 := by linarith [h_deg1, hG_deg_u]
    rw [← degree_congr_dec (instDecidableRelFinAdjToSimpleGraph _) (fun a b => Classical.propDecidable _)]
    omega
  · constructor
    · -- G'.degree v' = 3
      have h_deg2 : (toSimpleGraph g).degree v' = 4 := by rw [SimpleGraph.degree, ← degree_correct g v' h_valid.1 h_valid.2]; exact h_deg_v
      have h_step : 4 = (toSimpleGraph (g.remove_edge u' v')).degree v' + 1 := by linarith [h_deg2, hG_deg_v]
      rw [← degree_congr_dec (instDecidableRelFinAdjToSimpleGraph _) (fun a b => Classical.propDecidable _)]
      omega
    · constructor
      · -- ¬G'.Adj u' v'
        exact hG'_not_adj
      · -- G = add_edge G' u' v' h_neq
        exact hG_add

theorem apply_inv_method2_complete (g : AdjMat n) (G_prev : SimpleGraph (Fin n))
    (h_valid : Valid g) :
    Claim4GraphEnum.Spec.Method2_Rel G_prev (toSimpleGraph g) →
    ∃ g' ∈ AdjMat.apply_inv_method2 g, toSimpleGraph g' = G_prev := by
  rintro ⟨u, v, h_neq, h_deg_u, h_deg_v, h_not_adj, h_G⟩
  have h_not_adj_get : (toSimpleGraph g).Adj u v := by
    rw [h_G]
    apply Or.inr; apply Or.inl; exact ⟨rfl, rfl⟩
  have h_get_uv : g.get u v = true := by
    rw [← adj_iff_get g u v h_valid.1 h_valid.2]
    exact h_not_adj_get
  have h_get_vu : g.get v u = true := by
    rw [h_valid.1]
    exact h_get_uv

  have h_gu : g.degree u = 4 := by
    have hd_g : g.degree u = (toSimpleGraph g).degree u := degree_correct g u h_valid.1 h_valid.2
    have hd : (toSimpleGraph g).degree u = 4 := by
      letI : DecidableRel G_prev.Adj := fun a b => Classical.propDecidable _
      letI : DecidableRel (add_edge G_prev u v h_neq).Adj := fun a b => Classical.propDecidable _
      rw [degree_congr h_G u, SimpleGraph.degree]
      rw [Claim4GraphEnum.Spec.neighborFinset_add_edge]
      have hnot : v ∉ G_prev.neighborFinset u := by intro hc; apply h_not_adj; rwa [SimpleGraph.mem_neighborFinset] at hc
      rw [Finset.card_insert_of_notMem hnot]
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have heq : G_prev.degree u = @SimpleGraph.degree _ G_prev u (G_prev.neighborSetFintype u) := by congr
      rw [heq, h_deg_u]
    rw [hd_g, hd]

  have h_gv : g.degree v = 4 := by
    have hd_g : g.degree v = (toSimpleGraph g).degree v := degree_correct g v h_valid.1 h_valid.2
    have hd : (toSimpleGraph g).degree v = 4 := by
      letI : DecidableRel G_prev.Adj := fun a b => Classical.propDecidable _
      letI : DecidableRel (add_edge G_prev u v h_neq).Adj := fun a b => Classical.propDecidable _
      rw [degree_congr h_G v, SimpleGraph.degree]
      rw [Claim4GraphEnum.Spec.neighborFinset_add_edge_symm]
      have hnot : u ∉ G_prev.neighborFinset v := by
        intro hc
        apply h_not_adj
        have h1 : G_prev.Adj v u := by rwa [SimpleGraph.mem_neighborFinset] at hc
        exact G_prev.symm h1
      rw [Finset.card_insert_of_notMem hnot]
      rw [SimpleGraph.card_neighborFinset_eq_degree]
      have heq : G_prev.degree v = @SimpleGraph.degree _ G_prev v (G_prev.neighborSetFintype v) := by congr
      rw [heq, h_deg_v]
    rw [hd_g, hd]
  by_cases h_lt : u.val < v.val
  · use g.remove_edge u v
    constructor
    · simp only [AdjMat.apply_inv_method2, List.mem_map, List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and]
      use ⟨u, v⟩
      constructor
      · use u
        constructor
        · exact beq_iff_eq.mpr h_gu
        · use v
          constructor
          · exact beq_iff_eq.mpr h_gv
          · simp [h_lt, h_get_uv]
      · rfl
    · ext a b
      rw [toSimpleGraph_remove_edge]
      have h1 : (toSimpleGraph g).Adj a b ↔ G_prev.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        rw [h_G]
        exact Iff.rfl
      rw [h1]
      constructor
      · rintro ⟨h_or, h_ne1, h_ne2⟩
        rcases h_or with h | h | h
        · exact h
        · contradiction
        · contradiction
      · intro h
        refine ⟨Or.inl h, ?_, ?_⟩
        · rintro ⟨rfl, rfl⟩; exact h_not_adj h
        · rintro ⟨rfl, rfl⟩; exact h_not_adj h.symm
  · have h_lt2 : v.val < u.val := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (fun h => h_neq (Fin.ext h).symm)
    use g.remove_edge v u
    constructor
    · simp only [AdjMat.apply_inv_method2, List.mem_map, List.mem_flatMap, List.mem_filterMap, List.mem_filter, List.mem_finRange, true_and]
      use ⟨v, u⟩
      constructor
      · use v
        constructor
        · exact beq_iff_eq.mpr h_gv
        · use u
          constructor
          · exact beq_iff_eq.mpr h_gu
          · simp [h_lt2, h_get_vu]
      · rfl
    · ext a b
      rw [toSimpleGraph_remove_edge]
      have h1 : (toSimpleGraph g).Adj a b ↔ G_prev.Adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
        rw [h_G]
        exact Iff.rfl
      rw [h1]
      constructor
      · rintro ⟨h_or, h_ne1, h_ne2⟩
        rcases h_or with h | h | h
        · exact h
        · contradiction
        · contradiction
      · intro h
        refine ⟨Or.inl h, ?_, ?_⟩
        · rintro ⟨rfl, rfl⟩; exact h_not_adj (G_prev.symm h)
        · rintro ⟨rfl, rfl⟩; exact h_not_adj h

theorem apply_inv_method3b_sound (g : AdjMat (n + 1)) (g' : AdjMat n)
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_inv_method3b g →
    Claim4GraphEnum.Spec.Method3b_Rel (toSimpleGraph g') (toSimpleGraph g) := by
  intro _hmem
  -- apply_inv_method3b iterates over adjacent vertex pairs u, v with degree 3
  -- and checks if they don't share common neighbors.
  -- g' is thus a graph where u and v are contracted into a single vertex of degree 4.
  sorry

theorem apply_inv_method3b_complete (g : AdjMat (n + 1)) (G_prev : SimpleGraph (Fin n))
    (h_valid : Valid g) :
    Claim4GraphEnum.Spec.Method3b_Rel G_prev (toSimpleGraph g) →
    ∃ g' ∈ AdjMat.apply_inv_method3b g, toSimpleGraph g' = G_prev := by
  rintro ⟨_cfg, _h_cfg_eq⟩
  -- cfg provides the split vertex w and partitions N1, N2 in G_prev
  -- We need to find the specific pair of valid contracted vertices u, v in g
  sorry

theorem apply_inv_method1_sound (g : AdjMat (n + 2)) (g' : AdjMat n)
    (h_valid : Valid g) :
    g' ∈ AdjMat.apply_inv_method1 g →
    Claim4GraphEnum.Spec.Method1_Rel (toSimpleGraph g') (toSimpleGraph g) := by
  intro _hmem
  -- apply_inv_method1 iterates over K4 subgraphs in g
  -- g' is a graph where the K4 is transformed into two adjacent degree 3 vertices
  sorry

theorem apply_inv_method1_complete (g : AdjMat (n + 2)) (G_prev : SimpleGraph (Fin n))
    (h_valid : Valid g) :
    Claim4GraphEnum.Spec.Method1_Rel G_prev (toSimpleGraph g) →
    ∃ g' ∈ AdjMat.apply_inv_method1 g, toSimpleGraph g' = G_prev := by
  rintro ⟨_cfg, _h_Rel⟩
  -- cfg provides the vertex replacements v1, v2 and external neighbors X1, X2 in G_prev
  -- We need to find the specific K4 vertices in g
  sorry

-- ============================================================
-- 13. reduce_iso の公理
-- ============================================================

axiom reduce_iso_soundness (S : List (AdjMat n)) :
  ∀ g ∈ S, ∃ g' ∈ AdjMat.reduce_iso S,
    Nonempty (toSimpleGraph g ≃g toSimpleGraph g')

axiom reduce_iso_preserves_valid (S : List (AdjMat n)) :
  (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.reduce_iso S, Valid g'

-- ============================================================
-- 14. step_* ラッパー関数の Valid 保存
-- ============================================================

theorem step_method2_preserves_valid (S : List (AdjMat n)) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_method2 S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_method2]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_method2_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

theorem step_method3b_preserves_valid (S : List (AdjMat n)) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_method3b S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_method3b]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_method3b_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

theorem step_method1_preserves_valid (S : List (AdjMat n)) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_method1 S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_method1]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_method1_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

theorem step_inv_method2_preserves_valid (S : List (AdjMat n)) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_inv_method2 S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_inv_method2]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_inv_method2_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

theorem step_inv_method3b_preserves_valid (S : List (AdjMat (n + 1))) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_inv_method3b S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_inv_method3b]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_inv_method3b_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

theorem step_inv_method1_preserves_valid (S : List (AdjMat (n + 2))) :
    (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.step_inv_method1 S, Valid g' := by
  intro h_valid; simp only [AdjMat.step_inv_method1]
  intro g' hg'
  apply reduce_iso_preserves_valid
  · intro g hg
    obtain ⟨g_parent, hg_parent, hg_gen⟩ := List.mem_flatMap.mp hg
    exact apply_inv_method1_preserves_valid (h_valid g_parent hg_parent) g hg_gen
  · exact hg'

end Claim4GraphEnum.Correctness
