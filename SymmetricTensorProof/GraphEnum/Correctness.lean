import SymmetricTensorProof.GraphEnum.Impl
import SymmetricTensorProof.GraphEnum.Spec
import Mathlib

namespace GraphEnumeration

open SimpleGraph GraphEnumeration

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

instance (g : AdjMat n) : DecidableRel (toSimpleGraph g).Adj := by
  intro u v
  rw [toSimpleGraph_adj]
  infer_instance

-- AdjMat 名前空間内、または適当な場所に配置
theorem adj_iff_get {n} (g : AdjMat n) (u v : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, ¬g.get a a = true) :
    (toSimpleGraph g).Adj u v ↔ g.get u v = true := by
  -- toSimpleGraph の Adj の定義を展開
  rw [toSimpleGraph_adj]
  -- u = v かどうかで場合分け
  by_cases h_eq : u = v
  · -- u = v の場合: 左辺は定義よりFalse、右辺は非反射性(h_irref)よりFalse
    subst h_eq
    simp [h_irref]
  · -- u ≠ v の場合: 不等号条件はTrueになり、対称性で右辺を整理できる
    simp [h_eq]
    rw [h_symm v u]
    -- (A ∨ A) ↔ A なので整理完了
    simp

def Valid {n} (g : AdjMat n) : Prop :=
  (∀ u v, g.get u v = g.get v u) ∧ (∀ u, g.get u u = false)

theorem valid_empty {n} : Valid (GraphEnumeration.AdjMat.empty n) := by
  constructor
  · intro u v
    simp [GraphEnumeration.AdjMat.empty, GraphEnumeration.AdjMat.get, Array.getElem_replicate]
  · intro u
    simp [GraphEnumeration.AdjMat.empty, GraphEnumeration.AdjMat.get, Array.getElem_replicate]

theorem valid_add_edge {n} {g : AdjMat n} {u v : Fin n}
    (h_valid : Valid g) (h_ne : u ≠ v) : Valid (g.add_edge u v) := by
  constructor
  · -- 1. 対称性の証明
    intro x y
    -- get_add_edge 補題を使って展開
    simp only [GraphEnumeration.AdjMat.get_add_edge]
    -- 元のグラフの対称性 (g.get x y = g.get y x) を適用
    rw [h_valid.1 x y]
    -- 論理式の形: (G || (X=U ∧ Y=V) || (X=V ∧ Y=U)) = (G || (Y=U ∧ X=V) || (Y=V ∧ X=U))
    -- これらは AND/OR の順序が違うだけなので、可換性 (comm) で解ける
    simp [and_comm]
    conv =>
      lhs
      rw [Bool.or_right_comm]
  · -- 2. 非反射性の証明 (対角成分は false)
    intro x
    simp only [GraphEnumeration.AdjMat.get_add_edge]
    -- 元のグラフの非反射性 (g.get x x = false) を適用
    rw [h_valid.2 x]
    simp only [Bool.false_or] -- false || P -> P に簡約
    -- 残る式: (x = u ∧ x = v) ∨ (x = v ∧ x = u)
    -- これが true になると仮定して矛盾を導く
    by_contra h
    simp only [Bool.not_eq_false, Bool.or_eq_true, decide_eq_true_iff] at h
    -- どちらのケースでも x = u かつ x = v となるため u = v が導かれる
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h_ne rfl      -- u = v なので矛盾
    · exact h_ne rfl.symm -- v = u なので矛盾

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

/-
Task A: Degree correctness
The degree computed by AdjMat matches the degree in the SimpleGraph model.
-/
theorem degree_correct {n} (g : AdjMat n) (u : Fin n)
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, ¬g.get a a) :
    g.degree u = ((toSimpleGraph g).neighborFinset u).card := by
  -- First, prove that g.degree u counts the 'true' entries in the u-th row.
  have h_deg_eq_card : g.degree u = (Finset.univ.filter (fun v => g.get u v)).card := by
    simp only [AdjMat.degree]
    let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
    let row := g.data[row_idx]
    -- Equate foldl to sum of indicators
    have h_fold : row.foldl (fun count b ↦ if b then count + 1 else count) 0 =
        (row.toList.map (fun b ↦ if b then 1 else 0)).sum := by
      -- Array.foldl is essentially List.foldl on toList
      have h_tolist :
        row.foldl (fun count b ↦ if b then count + 1 else count) 0 =
        row.toList.foldl (fun count b ↦ if b then count + 1 else count) 0 := by
        simp [Array.foldl_toList]
      rw [h_tolist]
      have aux : ∀ (l : List Bool) (c : Nat),
        List.foldl (
            fun count b ↦ if b then count + 1 else count) c l
              = c + (l.map (fun b ↦ if b then 1 else 0)).sum := by
        intro l
        induction l with
        | nil => simp
        | cons h t ih => intro c; simp [ih]; split_ifs <;> simp [add_assoc]
      rw [aux row.toList 0]
      simp
    rw [h_fold]
    -- Equate Finset card to sum of indicators
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    -- We want to transform the List sum to a Finset sum over Fin n
    rw [← List.sum_ofFn]
    · -- Map the indices
      congr 1
      apply List.ext_get
      · rw [List.length_map, List.length_ofFn]
        rw [← g.h_size.2 row_idx]
        simp
        unfold row
        rfl
      · intro i h1 h2
        simp
        simp at h1 h2
        simp [row, row_idx]
        conv =>
          rhs
          unfold GraphEnumeration.AdjMat.get
          simp
  rw [h_deg_eq_card]
  congr 1
  ext v
  rw [SimpleGraph.mem_neighborFinset]
  rw [toSimpleGraph_adj]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h_get
    refine ⟨?_, ?_⟩
    · left; exact h_get
    · intro h_eq; rw [h_eq] at h_get; exact h_irref _ h_get
  · rintro ⟨(h_get | h_get_symm), h_ne⟩
    · exact h_get
    · rw [h_symm] at h_get_symm; exact h_get_symm

/-
Task B: Filtering functions correctness
-/
theorem get_isolated_correct {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n))
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, ¬g.get a a) :
    (AdjMat.get_isolated g v1 forbidden).toFinset =
    (Finset.univ.filter (fun (v : Fin n) =>
      ((toSimpleGraph g).neighborFinset v).card = 0 ∧ v ≠ v1 ∧ v ∉ forbidden)) := by
  unfold AdjMat.get_isolated
  ext x
  simp
  rw [degree_correct g x h_symm h_irref]
  simp [and_assoc]


theorem get_unused_correct {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n))
    (h_symm : ∀ a b, g.get a b = g.get b a)
    (h_irref : ∀ a, ¬g.get a a) :
    (AdjMat.get_unused g v1 forbidden).toFinset =
    (Finset.univ.filter (fun v =>
      let deg := (toSimpleGraph g).neighborFinset v |>.card
      1 ≤ deg ∧ deg ≤ 3 ∧
      ¬(toSimpleGraph g).Adj v1 v ∧ v ≠ v1 ∧ v ∉ forbidden)) := by
  unfold AdjMat.get_unused
  rw [List.toFinset_filter]
  ext x
  simp
  rw [degree_correct g x h_symm h_irref]
  simp [toSimpleGraph_adj]
  simp [h_symm]
  rw [and_assoc]
  conv =>
    lhs
    rw [and_assoc]
    rw [and_assoc]
  have : g.get v1 x = false ∧ ¬ x = v1  ↔ (g.get v1 x = true → v1 = x) ∧ ¬ x = v1 := by
    constructor
    · intro h_get
      rcases h_get with ⟨h_get, h_neq⟩
      rw [h_get]
      tauto
    · intro h_get
      rcases h_get with ⟨h_get, h_neq⟩
      constructor
      · -- ゴール 1: g.get v1 x = false を示す
        by_cases h : g.get v1 x = true
        · -- もし true だとすると、h_get より v1 = x となり、h_neq と矛盾する
          have h_eq : v1 = x := h_get h
          exact False.elim (h_neq h_eq.symm)
        · -- もし true でなければ、Bool の性質から false である
          simp at h
          exact h
      · -- ゴール 2: ¬v1 = x を示す
        -- これは仮定 h_neq そのもの
        exact h_neq
  have :
    g.get v1 x = false ∧ ¬ x = v1 ∧ x ∉ forbidden
      ↔ (g.get v1 x = true → v1 = x) ∧ ¬ x = v1 ∧ x ∉ forbidden := by
    constructor
    · intro h_get
      rcases h_get with ⟨h_get, h_neq, h_forbid⟩
      rw [h_get]
      tauto
    · intro h_get
      rcases h_get with ⟨h_get, h_neq, h_forbid⟩
      constructor
      · -- ゴール 1: g.get v1 x = false を示す
        by_cases h : g.get v1 x = true
        · -- もし true だとすると、h_get より v1 = x となり、h_neq と矛盾する
          have h_eq : v1 = x := h_get h
          exact False.elim (h_neq h_eq.symm)
        · -- もし true でなければ、Bool の性質から false である
          simp at h
          exact h
      · -- ゴール 2: ¬v1 = x を示す
        -- これは仮定 h_neq そのもの
        exact And.intro h_neq h_forbid
  conv =>
    lhs
    arg 2
    arg 2
    rw [this]

-- (既存の証明の続き)

-- 以前の証明の続き

/-
Helper lemma: The list filtering logic in Impl matches Spec via boolean reflection.
-/
theorem list_filter_congr {α}
  (l : List α) (p_bool : α → Bool) (p_prop : α → Prop) [DecidablePred p_prop]
    (h_iff : ∀ x ∈ l, p_bool x = true ↔ p_prop x) :
    l.filter p_bool = l.filter (fun x => decide (p_prop x)) := by
  apply List.filter_congr
  intro x hx
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_iff]
  exact h_iff x hx

/-
  空グラフの整合性
-/
lemma empty_correct : toSimpleGraph (AdjMat.empty n) = SimpleGraph.fromEdgeSet ∅ := by
  -- AdjMat.empty は全て false なので、エッジ集合は空になる
  ext u v
  simp [toSimpleGraph, SimpleGraph.fromRel, AdjMat.empty, AdjMat.get]

/-
Main Correctness Theorem for generate_next_graphs.
We prove strict List equality to match Spec.
証拠のインスタンスの違いで証明にてこずった。見た目は同じなのに変形できないケースで参考になるかも。
-/
theorem generate_next_graphs_correct {n}
  (g : AdjMat n)
  (v1 : Fin n)
  (forbidden : List (Fin n))
  (h_symm : ∀ a b, g.get a b = g.get b a)
  (h_irref : ∀ a, ¬g.get a a) :
    (g.generate_next_graphs v1 forbidden).map toSimpleGraph =
    GraphEnumeration.generate_next_graphs (toSimpleGraph g) v1 forbidden := by

  -- 1. 定義の展開
  unfold AdjMat.generate_next_graphs
  unfold GraphEnumeration.generate_next_graphs

  -- 2. 等価性の補題を用意 (中身は別途証明するとして sorry のままにしてあります)
  have h_iso_eq : (g.get_isolated v1 forbidden) =
      (Finset.univ.filter
        (fun v =>
          ((toSimpleGraph g).neighborFinset v).card = 0
            ∧ v ≠ v1 ∧ v ∉ forbidden)).sort (· ≤ ·) := by

    -- 1. 余計な変形はせず、まず定義だけ展開して「List = List」の形をはっきりさせます
    dsimp [AdjMat.get_isolated]

    -- 2. ここでいきなり「最強の武器」を使います
    --    「中身が同じ」かつ「両方ソート済み」ならリストは等しい
    apply List.Perm.eq_of_pairwise (le := (· ≤ ·))

    -- 【ゴール1: 反対称性】(a ≤ b かつ b ≤ a なら a = b)
    · intro a b _ _ hab hba
      exact le_antisymm hab hba

    -- 【ゴール2: 左辺がソート済み】
    -- 左辺は finRange (ソート済み) を filter したものなので、ソート済みです
    · apply List.Pairwise.filter
      apply List.Pairwise.imp (R := (· < ·))
      · intro a b; exact le_of_lt -- (< ならば ≤)
      · exact List.pairwise_lt_finRange n -- (finRange は < でソート済み)

    -- 【ゴール3: 右辺がソート済み】
    · exact Finset.pairwise_sort _ (· ≤ ·)

    -- 【ゴール4: 中身が同じ (Permutation)】
    · -- 1. List.Perm を Multiset の等式 (↑l₁ = ↑l₂) に変換します
      -- 矢印「←」を使って、定理の右辺(Perm)を左辺(Eq)に書き換えます
      rw [← Multiset.coe_eq_coe]

      -- 2. ゴールが Multiset になったので、sort を剥がせます
      -- (↑(s.sort r) = s.val)
      rw [Finset.sort_eq]

      -- 4. 全体集合 (finRange n vs Finset.univ) の整合性を取ります
      simp only [Finset.univ, Fintype.elems, Finset.filter_val]

      have h_match :
        (List.filter (
          fun v ↦ g.degree v == 0 && !v == v1 && !List.elem v forbidden) (List.finRange n)) =
        (List.filter (
          fun v ↦ decide (g.degree v = 0 ∧ ¬v = v1 ∧ v ∉ forbidden)) (List.finRange n)) := by
        apply List.filter_congr
        intro v _
        -- Bool と Prop の変換 (&& ↔ ∧, == ↔ =, ! ↔ ¬)
        -- Bool.and_assoc でカッコのズレを直し、beq_iff_eq で == を = に直す
        simp only [Bool.decide_and]
        -- List.elem v forbidden が v ∈ forbidden になるのを処理
        simp
        have h_deg_decide : (g.degree v == 0) = decide (g.degree v = 0) := by
          by_cases h : g.degree v = 0
          · symm
            simp [h]
          · simp [h]
        have h_notv_decide : (!v == v1) = !decide (v = v1) := by
          by_cases h : v = v1
          · simp [h]
          · simp [h]
        simp [h_deg_decide, h_notv_decide, Bool.and_assoc]

      -- 5. これで両辺が Multiset.filter 同士になったので、中身の条件比較へ
      simp only [h_match, <- Multiset.filter_coe]
      apply Multiset.filter_congr
      intro v _
      rw [degree_correct g v h_symm h_irref]
      simp

  have h_unused_eq : (g.get_unused v1 forbidden) =
      (Finset.univ.filter (fun v =>
        let deg := ((toSimpleGraph g).neighborFinset v).card
        1 ≤ deg ∧ deg ≤ 3 ∧
        ¬(toSimpleGraph g).Adj v1 v ∧ v ≠ v1 ∧ v ∉ forbidden)).sort (· ≤ ·) := by
    -- 1. 定義展開
    unfold AdjMat.get_unused
    -- 2. 「ソート済み」かつ「中身が同じ」ならリストは等しい
    apply List.Perm.eq_of_pairwise (le := (· ≤ ·))

    -- 【ゴール1: 反対称性】
    · intro a b _ _ hab hba
      exact le_antisymm hab hba

    -- 【ゴール2: 左辺がソート済み】(finRange の filter なので自明)
    · apply List.Pairwise.filter
      apply List.Pairwise.imp (R := (· < ·))
      · intro a b; exact le_of_lt
      · exact List.pairwise_lt_finRange n

    -- 【ゴール3: 右辺がソート済み】(Finset.sort なので自明)
    · exact Finset.pairwise_sort _ (· ≤ ·)

    -- 【ゴール4: 中身が同じ (Permutation)】
    · -- 1. Multiset の等式へ
      rw [← Multiset.coe_eq_coe]
      rw [Finset.sort_eq, Finset.filter_val]
      simp only [Finset.univ, Fintype.elems]

      -- 2. Bool (LHS) と Prop (RHS) の条件式のすり合わせ
      --    get_unused の実装は推測ですが、おそらく degree や get の Bool 版を使っているはずです
      have h_match :
        (List.filter (fun v ↦
          -- ここは実際の get_unused の実装に合わせて調整してください
          -- 一般的には (1 <= degree && degree <= 3 && !get v1 v && !v == v1 && !elem) のはず
          g.degree v ≥ 1 && g.degree v ≤ 3 && !g.get v1 v && !v == v1 && !List.elem v forbidden
        ) (List.finRange n)) =
        (List.filter (fun v ↦ decide (
          -- こちらはターゲットの Prop
          1 ≤ g.degree v ∧ g.degree v ≤ 3 ∧ ¬g.get v1 v ∧ ¬v = v1 ∧ v ∉ forbidden
        )) (List.finRange n)) := by
          apply List.filter_congr
          intro v _
          -- Bool.and_assoc, decide_and 等で Bool式 と Prop(decide) を一致させる
          simp only [Bool.decide_and]
          -- List.elem, ge, le などの表記揺れを吸収
          simp
          have h_notv_decide : (!v == v1) = !decide (v = v1) := by
            by_cases h : v = v1
            · simp [h]
            · simp [h]
          rw [h_notv_decide, <- Bool.and_assoc, <- Bool.and_assoc, Bool.and_assoc]


      -- 3. すり合わせた式を適用
      rw [h_match]
      rw [← Multiset.filter_coe]

      -- 4. 中身 (Prop) の比較
      apply Multiset.filter_congr
      intro v _

      -- degree の定義を SimpleGraph 側に合わせる
      rw [degree_correct g v h_symm h_irref]
      have : (¬ v = v1) = (v ≠ v1) := by simp
      rw [this]
      have : (¬ g.get v1 v) = (¬ (toSimpleGraph g).Adj v1 v) := by
        -- 1. 右辺の Adj を get に書き換える
        rw [adj_iff_get g v1 v h_symm h_irref]
      rw [this]



  -- 3. 【重要】 分岐する前に、左辺(Impl)の項をすべて右辺(Spec)の形に書き換える
  -- これにより、左右の式が「同じリストに対する match」の形になります
  rw [h_iso_eq, h_unused_eq]
  dsimp only
  simp
  set iso_term := (Finset.univ.filter (fun v =>
    (toSimpleGraph g).degree v = 0 ∧ ¬ v = v1 ∧ v ∉ forbidden
  )).sort (· ≤ ·)
  -- 4. 共通になった「isolated リスト」に対して cases を行う
  -- こうすることで、h_iso などの仮定を使わずとも、自動的に両辺が同じ分岐に入ります
  cases h_iso : iso_term with
  | nil =>
    simp
    congr 1
    · funext x; dsimp; apply add_edge_correct

    · let expected := (Finset.univ.filter (fun v ↦
          1 ≤ (toSimpleGraph g).degree v ∧
          (toSimpleGraph g).degree v ≤ 3 ∧
          ¬(toSimpleGraph g).Adj v1 v ∧
          ¬ v = v1 ∧
          v ∉ forbidden)).sort (· ≤ ·)

      change expected = _

      -- 【ここが解決の鍵】
      -- 項の一致を確認する rw / generalize を捨て、
      -- 強制的にケース分割する split を使います。
      split

      -- ケース1: [] の場合 (一致するので終了)
      · unfold expected
        -- 1. congruency (一致性) を強力に適用して、sort や filter の皮を剥ぎます
        congr!

      -- ケース2: h :: tail の場合 (h_iso と矛盾させて終了)
      · next h tail h_cons =>
        exfalso
        -- ここだけ convert で「意味的な等価性」を使ってすり抜けます
        have h_contra : [] = h :: tail := by
          rw [← h_cons]
          convert h_iso.symm
        contradiction

  | cons h tail =>
    -- 1. 右辺の match を強制的に分解
    split

    -- ケース: match が [] の場合 (矛盾するので消える)
    · simp_all

    -- ケース: match が h_match :: t_match の場合
    · next h_match t_match h_eq =>
      simp_all
      split
      -- ケース 2-1: リストが [] になった場合
      -- しかし h_iso (リスト = h_match :: t_match) があるので、これは矛盾します。
      · next h_empty =>
        -- h_empty : {v | ...}.toList = []
        -- h_iso   : iso_term = h_match :: t_match

        -- 1. h_iso の中の iso_term を定義通りに展開します
        dsimp [iso_term] at *

        -- 2. h_empty を使って h_iso を書き換えます
        -- これで h_iso が `[] = h_match :: t_match` になり、矛盾が明白になります
        have h_contra : [] = h_match :: t_match := by
          -- 1. h_empty を逆向きに使って、[] を { ... }.toList に戻す
          rw [← h_empty]

          -- 2. convert を使って h_iso を無理やり適用する
          -- これにより、ゴールは「判定方法（インスタンス）の違い」の証明に変わります
          -- なぜかこれで解決したのでダメな時は試してみる価値あり
          convert h_iso

        -- 3. 矛盾により証明終了
        contradiction

      -- ケース 2-2: 内側のリストが h_head :: h_tail (証明ケース)
      · next h_head h_tail h_cons =>
        -- 1. 定義を展開して視界を合わせる
        dsimp [iso_term] at *

        -- 【修正箇所】
        -- rw でのマッチングを諦め、calc ブロックで強制的に等式を繋ぎます。
        -- これなら「検索」が発生しないので失敗しません。
        have h_list_eq : h_match :: t_match = h_head :: h_tail := by
          calc h_match :: t_match
            _ = (Finset.univ.filter (
                fun v => (toSimpleGraph g).degree v = 0
                  ∧ ¬ v = v1 ∧ v ∉ forbidden)).sort (· ≤ ·) := by
              -- h_iso の逆方向を使います。型が微妙に違っても convert が吸収します。
              convert h_iso.symm
            _ = h_head :: h_tail := by
              -- h_cons を使います。
              convert h_cons

        -- リストが等しいなら、中身も等しい
        rcases h_list_eq with ⟨rfl, rfl⟩

        -- これで変数が h_match, t_match に統一されたのでゴールが通ります
        simp_all
        constructor

        -- 先頭 (Head)
        · apply add_edge_correct

        -- 残り (Tail)
        · congr 1
          · ext x
            dsimp
            rw [add_edge_correct]
          · congr!

theorem transition_correct {n}
  (S : List (AdjMat n)) (v1 : Fin n) (forbidden : List (Fin n))
  (h_valid : ∀ g ∈ S, (∀ a b, g.get a b = g.get b a) ∧ (∀ a, ¬g.get a a)) :
    (AdjMat.transition S v1 forbidden).map toSimpleGraph =
    GraphEnumeration.transition (S.map toSimpleGraph) v1 forbidden := by
  dsimp [AdjMat.transition, GraphEnumeration.transition]
  rw [List.map_flatMap]
  conv_rhs => rw [List.flatMap_map]
  -- 「リストの各要素 g について、変換結果が等しい」ことを示す
  apply List.flatMap_congr
  intro g hg
  -- 仮定から性質を取り出し、前回の定理を適用
  obtain ⟨h_symm, h_irref⟩ := h_valid g hg
  exact generate_next_graphs_correct g v1 forbidden h_symm h_irref

/-
  3. Reduce Iso の整合性 (Axiom)

  Spec と Impl の両方で opaque になっているため、
  「Impl側で削減して変換したもの」と「変換してからSpecで削減したもの」が
  等価であることを公理として要請します。
-/
axiom reduce_iso_commutes {n} (S : List (AdjMat n)) (anchors : List (Fin n)) :
  (AdjMat.reduce_iso S anchors).map toSimpleGraph =
  GraphEnumeration.reduce_iso (S.map toSimpleGraph) anchors

/-
  ヘルパー: リストのフィルタリングが明示的なリストと一致することの証明
  (入力リストに重複がないことを前提とします)
-/
lemma forbidden_filter_eq_list (v1 v2 v3 v4 : Fin n)
  (h_nodup : [v1, v2, v3, v4].Nodup) :
  let all := [v1, v2, v3, v4]
  (all.filter (· != v1)) = [v2, v3, v4] := by
  simp
  -- Nodup を使って v1 ≠ v2, v1 ≠ v3 ... を示し、filterの結果を確定させる
  have h_neq_v12 : v1 ≠ v2 := by intro h; subst h; simp at h_nodup
  have h_neq_v13 : v1 ≠ v3 := by intro h; subst h; simp at h_nodup
  have h_neq_v14 : v1 ≠ v4 := by intro h; subst h; simp at h_nodup
  -- 単純化
  simp [h_neq_v12.symm, h_neq_v13.symm, h_neq_v14.symm]


-- reduce_iso の公理（定義変更に合わせて型のみ適合）
axiom reduce_iso_preserves_valid (S : List (AdjMat n)) (anchors : List (Fin n)) :
  (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.reduce_iso S anchors, Valid g'

-- transition の補題
-- 変更点: g.get u u = false に対応し、cands に v が含まれないことを前提に追加
/-
theorem transition_preserves_valid (S : List (AdjMat n)) (v : Fin n) (forbidden : List (Fin n)) :
  (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.transition S v forbidden, Valid g'
-/
theorem transition_preserves_valid (S : List (AdjMat n)) (v : Fin n) (forbidden : List (Fin n)) :
  (∀ g ∈ S, Valid g) → ∀ g' ∈ AdjMat.transition S v forbidden, Valid g' := by
  intro h_valid g' hg'
  -- 1. transition (flatMap) の分解
  simp [AdjMat.transition, List.mem_flatMap] at hg'
  rcases hg' with ⟨g, hg_mem, h_gen⟩
  -- 2. generate_next_graphs (map) の分解
  -- ここで unfold してから map のメンバシップを展開するのがコツです
  unfold AdjMat.generate_next_graphs at h_gen
  rw [List.mem_map] at h_gen
  rcases h_gen with ⟨u, hu_mem, h_eq⟩
  subst h_eq
  -- 3. u ≠ v の証明
  -- u は get_isolated か get_unused の結果に含まれているため、
  -- 定義にある filter (· != v) により u ≠ v が保証される
  have h_u_ne_v : u ≠ v := by
    -- match 式の分岐を処理
    split at hu_mem
    · -- case: isolated = [] -> u ∈ unused
      simp [AdjMat.get_unused] at hu_mem
      rcases hu_mem with ⟨_, res⟩
      -- Boolの && 連鎖から !(u == v) を取り出す
      simp_all
    · -- case: isolated = h :: tail -> u ∈ h :: unused
      -- u が h なのか unused なのかで分岐
      rename_i h tail heq -- マッチの結果を名前付け
      simp [AdjMat.get_isolated] at heq
      simp at hu_mem
      cases hu_mem with
      | inl h_eq =>
        -- u = h の場合
        -- 1. まず、h が h :: tail に含まれるという自明な事実を作る
        have h_in : h ∈ h :: tail := List.mem_cons_self
        -- 2. heq (filter ... = h :: tail) を使って、
        --    リスト側(h::tail) を filter式 に書き戻す (←heq)
        rw [←heq] at h_in
        -- filter の条件から !(h == v) を取り出す
        simp at h_in
        subst h_eq
        exact h_in.1.2
      | inr h_in_unused =>
        -- u ∈ unused の場合
        simp [AdjMat.get_unused] at h_in_unused
        rcases h_in_unused with ⟨_, res⟩
        simp_all
  -- 4. Valid の保存証明
  have hg := h_valid g hg_mem
  constructor
  -- 対称性
  · intro a b
    rw [AdjMat.get_add_edge, AdjMat.get_add_edge, hg.1 a b]
    simp only [Bool.or_comm, Bool.or_left_comm]
    have : decide (a = u ∧ b = v) = decide (b = v ∧ a = u) := by
      simp [Bool.and_comm]
    rw [←this]
    have : decide (a = v ∧ b = u) = decide (b = u ∧ a = v) := by
      simp [Bool.and_comm]
    rw [←this]
  -- 非反射性 (自己ループなし)
  · intro a
    rw [AdjMat.get_add_edge]
    rw [hg.2 a] -- g は valid なので false
    simp only [Bool.false_or, <-Bool.decide_or, decide_eq_false_iff_not]
    rw [and_comm, or_self_iff]
    simp
    by_cases h_a_eq_u : a = u
    · simp [h_a_eq_u, h_u_ne_v]
    · simp [h_a_eq_u]

-- タクティクの強化
-- transition_preserves_valid が要求する「候補リストに v が含まれない」証明を
-- simp [*] で自動処理するように変更
-- 正しい solve_validity マクロの定義
macro "solve_validity" : tactic =>
  `(tactic| repeat (
      first
      | apply reduce_iso_preserves_valid
      | apply transition_preserves_valid
      | { -- ベースケース: ∀ g ∈ [empty], Valid g の処理
          intro g hg
          simp at hg
          subst hg
          apply valid_empty
        }
    ))
/-
  4. メインの正当性定理

  入力リストが同一であれば、Implの出力(を変換したもの)とSpecの出力は一致する。
-/
theorem enumerate_Gamma_4_4_correct (v_list : List (Fin n))
  (h_nodup : v_list.Nodup) :
  (AdjMat.enumerate_Gamma_4_4 n v_list).map toSimpleGraph =
  GraphEnumeration.enumerate_Gamma_4_4 v_list := by
  match v_list with
  | [] => simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4]
  | [v1] => simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4]
  | [v1, v2] => simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4]
  | [v1, v2, v3] => simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4]
  -- メインケース: [v1, v2, v3, v4]
  | [v1, v2, v3, v4] =>
    -- 定義を展開
    simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4, GraphEnumeration.S_0_0]
    -- 2. Nodup から全ての「頂点が異なる」事実を取り出す
    simp only [List.nodup_cons, List.mem_cons, not_or, List.nodup_nil] at h_nodup
    rcases h_nodup with ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, ⟨h34⟩, -⟩
    -- 3. 不等式を使って filter を簡約する (ここからは前回と同じ)
    simp [h12, h13, h14, h23, h24, h34]
    have h21 : ¬ v2 = v1 := ne_comm.mp h12
    have h31 : ¬ v3 = v1 := ne_comm.mp h13
    have h41 : ¬ v4 = v1 := ne_comm.mp h14.1
    have h32 : ¬ v3 = v2 := ne_comm.mp h23
    have h42 : ¬ v4 = v2 := ne_comm.mp h24.1
    have h43 : ¬ v4 = v3 := ne_comm.mp h34
    have h_v1_filter : List.filter (fun x ↦ x != v1) [v2, v3, v4] = [v2, v3, v4] := by
      simp
      exact ⟨h21, h31, h41⟩
    have h_v2_filter : List.filter (fun x ↦ x != v2) [v3, v4] = [v3, v4] := by
      simp
      exact ⟨h32, h42⟩
    have h_v3_filter : List.filter (fun x ↦ x != v3) [v4] = [v4] := by
      simp
      exact h43
    have : (⊥ : SimpleGraph (Fin n)) = SimpleGraph.fromEdgeSet ∅ := by
      -- 1. グラフの等価性を「任意の頂点 u, v 間の隣接関係の等価性」に変換する
      ext u v
      -- 2. 定義を展開して簡約する
      -- (⊥).Adj u v は False
      -- (fromEdgeSet ∅).Adj u v は (s(u, v) ∈ ∅) なので False
      simp
    have h_valid (g : AdjMat n) :
      (∀ u v, g.get u v = g.get v u) ∧ (∀ u, g.get u u = false) ↔ Valid g := by
      unfold Valid
      simp
    -- 4. 可換図式の適用 (Map押し込み)
    -- Step 4 (v4)
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    rw [reduce_iso_commutes]
    rw [transition_correct]
    -- 残りの処理
    simp only [List.map_cons, List.map_nil]
    rw [empty_correct]
    rw [h_v1_filter, h_v2_filter, h_v3_filter, this]
    · intro g hg
      simp at hg
      subst hg
      simp [h_valid, valid_empty]
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
    · simp only [Bool.not_eq_true]
      simp_rw [h_valid]
      solve_validity
  -- すべての具体的なケースの後に追加
  | _ :: _ :: _ :: _ :: _ :: _ =>
    -- 定義上、長さが4以外の入力に対しては空リストなどを返すようになっているはずなので、
    -- 定義を展開するだけで証明が終わるはずです。
    simp [AdjMat.enumerate_Gamma_4_4, GraphEnumeration.enumerate_Gamma_4_4]


end GraphEnumeration
