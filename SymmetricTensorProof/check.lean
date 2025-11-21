import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Logic.IsEmpty
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Order.Group.Unbundled.Basic

open scoped BigOperators
open Matrix

universe u

structure Params where (n t : ℕ) (ht₁ : 2 ≤ t) (ht₂ : t ≤ n-1)
abbrev Ground (P : Params) := Sym2 (Fin P.n)          -- E(Kₙ)
abbrev d_col (P : Params) : ℕ := P.t * (P.t+1) / 2        -- 行数
abbrev Var (P : Params) := Fin P.n × Fin P.t
abbrev K := ℚ
abbrev Kpoly (P : Params) := MvPolynomial (Var P) K

@[simp] lemma fin_nonempty_iff_pos (m : ℕ) :
  Nonempty (Fin m) ↔ 0 < m := by
  constructor
  · intro h
    rcases h with ⟨x⟩
    exact Nat.lt_of_le_of_lt (Nat.zero_le x.val) x.is_lt
  · intro h
    refine ⟨⟨0, h⟩⟩

@[simp] lemma fin_isEmpty_iff (m : ℕ) :
  IsEmpty (Fin m) ↔ m = 0 := by
  apply Iff.intro
  · intro h
    by_contra hm
    have hpos : 0 < m := Nat.pos_of_ne_zero hm
    let x : Fin m := ⟨0, hpos⟩
    have : False := h.elim x
    contradiction
  · intro hm
    rw [hm]
    exact Fin.isEmpty

/- `Ground P` は有限（`Finite` 版）。 -/
instance instFiniteGround (P : Params) : Finite (Ground P) := by
  dsimp [Ground]
  infer_instance   -- `Finite (Sym2 (Fin P.n))`

/- `Ground P` は有限（`Fintype` 版）。 -/
noncomputable instance instFintypeGround (P : Params) : Fintype (Ground P) :=
  Fintype.ofFinite (Ground P)

/- 便利のための可判別同値も生やしておくと後で困らない -/
noncomputable instance instDecEqGround (P : Params) : DecidableEq (Ground P) :=
  inferInstance

/- マトロイドの要素の基本パラメータ -/
structure Instance where
  P : Params
  edges : Finset (Ground P)   -- ← List ではなく Finset

namespace Instance

abbrev n (G : Instance) : ℕ := G.P.n
abbrev t (G : Instance) : ℕ := G.P.t
noncomputable def edgesList (G : Instance) : List (Ground G.P) := G.edges.toList

end Instance

/- 各テンソルをベクトル化した際の上三角 (r ≤ c) のインデックスの `List`（r 外側, c 内側） -/
def upperPairs (t : ℕ) : List { rc : Fin t × Fin t // rc.1 ≤ rc.2 } :=
  -- 外側：r を走査
  (List.finRange t).foldr
    (
      fun r acc =>
      -- 内側：c を走査
        (List.finRange t).foldr
          (
            fun c acc' =>
              -- 条件分岐：r ≤ c なら要素を1個 cons、そうでなければ何もしない
              if h : r ≤ c then
                ⟨(r, c), by simpa using h⟩ :: acc'
              else
                acc'
          )
          acc
    )
    []

/- `finRange t` を「`c < r` 側（fst）とそれ以外（snd）」に `partition` したとき，
    `fst ++ snd = finRange t` が成り立つ。 -/
lemma finRange_partition_lt_append (t r : ℕ) :
  let p : Fin t → Bool := fun c => decide ((c : ℕ) < r)
  let pr := (List.finRange t).partition p
  pr.fst ++ pr.snd = List.finRange t := by
  classical
  intro p pr
  -- t による帰納法
  induction t with
  | zero =>
    simp [List.finRange_zero, pr]
  | succ t ih =>
    -- 末尾要素
    let last : Fin (t+1) := ⟨t, Nat.lt_succ_self _⟩
    -- finRange (t+1) の標準分解
    have hs : List.finRange (t+1) = (List.finRange t).map Fin.castSucc ++ [last] := by
      simp [List.finRange_succ_last]
      rfl

    -- 末尾 `t` が r より小さいかで場合分け
    by_cases hlt : t < r
    case pos =>
      -- p last = true
      have hlast_true : p last = true := by
        dsimp [p]
        simp [last, hlt]
      -- `partition` を `filter` に展開し，`filter_append` と `hlast_true` で整理
      simp [hs]

      -- Fin t 上の対応述語
      let p0 : Fin t → Bool := fun c => p (Fin.castSucc c)

      -- A := (finRange t).map castSucc
      have hpA :
          List.filter p ((List.finRange t).map Fin.castSucc)
            = (List.finRange t).map Fin.castSucc := by
        -- すべて p を満たすので filter = self
        apply List.filter_eq_self.2
        intro x hx
        rcases List.mem_map.1 hx with ⟨c, hc, rfl⟩
        -- p (castSucc c) = decide (c.val < r) = true
        dsimp [p]
        -- c.is_lt : c.val < t
        have : (c : ℕ) < r := Nat.lt_trans c.is_lt hlt
        simpa [Fin.val_mk] using this

      have hnotA :
          List.filter (fun x => ! p x) ((List.finRange t).map Fin.castSucc) = [] := by
        -- すべて p を満たす ⇒ ¬p 側の filter は空
        apply List.filter_eq_nil_iff.2
        intro x hx
        rcases List.mem_map.1 hx with ⟨c, hc, rfl⟩
        dsimp [p]
        have : (c : ℕ) < r := Nat.lt_trans c.is_lt hlt
        -- decide (c.val < r) = true ⇒ !true = false
        simpa [Fin.val_mk]

      simp [pr, List.partition_eq_filter_filter, hs, List.filter_append,
            hlast_true, hpA]

      intro x
      have : x < t := Fin.is_lt x
      have : x < r := by
        exact Nat.lt_trans this (k := r) hlt
      simp [p, this]

    case neg =>
      -- p last = false （r ≤ t）
      have hlast_false : p last = false := by
        have : r ≤ t := Nat.le_of_not_lt hlt
        have : ¬ ((last : ℕ) < r) := not_lt.mpr (by simpa [Fin.val_mk] using this)
        dsimp [p]
        simp [this]

      -- Fin t 上の対応述語：p0 c := p (castSucc c) ＝ decide (c < r)
      let p0 : Fin t → Bool := fun c => p (Fin.castSucc c)
      let xs := List.finRange t
      -- IH を p0 版（filter で書いた形）に取り出す
      have ih₀ :
          ((List.finRange t).filter p0) ++
          ((List.finRange t).filter fun c => ! p0 c)
            = List.finRange t := by
        -- あなたの ih は「partition = filter/filter」に展開すれば一致
        simpa [p0, List.partition_eq_filter_filter] using ih

      -- map Fin.castSucc で IH を像へ送る
      have ih' :
          (((List.finRange t).filter p0).map Fin.castSucc) ++
          (((List.finRange t).filter fun c => ! p0 c).map Fin.castSucc)
            = (List.finRange t).map Fin.castSucc := by
        simpa [List.map_append] using congrArg (List.map Fin.castSucc) ih₀

      -- 「filter ∘ map = map ∘ filter」（castSucc を通す）２本
      -- p0 はそのまま：p0 c := p c.castSucc
      have filter_map_true :
          List.filter p (List.map Fin.castSucc xs)
        = List.map Fin.castSucc (List.filter p0 xs) := by
        classical
        -- xs について通常のリスト帰納法（前提なし）
        induction xs with
        | nil =>
            simp
        | cons c cs ih =>
            -- 先頭 c で p 判定の真偽に分けると両辺の if が一致し、尻尾は ih で潰れる
            cases h : p c.castSucc <;>
              simp [p0, List.map, List.filter, h, ih]

      -- 左の第1項を書き換える
      have filter_map_true' :
          List.filter p (List.map Fin.castSucc (List.finRange t))
            = List.map Fin.castSucc (List.filter p0 (List.finRange t)) := by
        simpa [xs] using filter_map_true   -- xs = finRange t を代入

      have filter_map_false :
          List.filter (fun x => ! p x) (List.map Fin.castSucc xs)
        = List.map Fin.castSucc (List.filter (fun c => ! p0 c) xs) := by
        classical
        induction xs with
        | nil =>
            simp
        | cons c cs ih =>
            cases h : p c.castSucc <;>
              simp [p0, List.map, List.filter, h, ih]

      have filter_map_false' :
        List.filter (not ∘ p) (List.map Fin.castSucc (List.finRange t)) =
          List.map Fin.castSucc (List.filter (fun c => ! p0 c) (List.finRange t)) := by
        simpa [Function.comp] using filter_map_false

      simp [pr, List.partition_eq_filter_filter, hs, List.filter_append,
            hlast_false, filter_map_false', <-List.append_assoc, filter_map_true', ih']

lemma length_filter_lt_finRange (r t : ℕ) :
  ((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).length
    = Nat.min r t := by
  classical
  induction t with
  | zero =>  simp
  | succ t ih =>
  -- 末尾要素
  let last : Fin (t+1) := ⟨t, Nat.lt_succ_self _⟩
  -- 標準分解
  have hs :
      List.finRange (t+1)
        = (List.finRange t).map Fin.castSucc ++ [last] := by
    simpa using List.finRange_succ_last (n := t)

  -- map 側の filter の長さはそのまま（castSucc で val は不変）
  have hmap :
      (((List.finRange t).map Fin.castSucc).filter
          (fun c : Fin (t+1) => decide ((c : ℕ) < r))).length
        = ((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).length := by
    -- （filter → map）にしてから length_map で消すと simp で落ちます
      have :
        (((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).map
            (fun c => (Fin.castSucc c : Fin (t+1))) ).length
          =
        ((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).length := by
        simp
      have cast_swap :
        ((List.finRange t).map Fin.castSucc).filter (fun c : Fin (t+1) => decide ((c : ℕ) < r)) =
        (((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).map
            (fun c => (Fin.castSucc c : Fin (t+1))) ) := by
        classical
        induction (List.finRange t) with
        | nil => simp
        | cons a as ih =>
            by_cases h : (a : ℕ) < r
            · simp [List.map, List.filter, h, ih]
            · simp [List.map, List.filter, h, ih]
      rw [cast_swap, this]


  -- 1 要素側の寄与： t < r なら 1、そうでなければ 0
  have hlast :
      ([last].filter (fun c : Fin (t+1) => decide ((c : ℕ) < r))).length
        = (if t < r then 1 else 0) := by
      by_cases htr : t < r
      · have : (last : Fin (t+1)) < r := by simpa [last] using htr
        simp [last, this]
      · have : ¬ ( (last : Fin (t+1)) < r ) := by simpa [last] using htr
        simp [last, this]

  -- まとめて帰納式
  have step :
      ((List.finRange (t+1)).filter (fun c : Fin (t+1) => decide ((c : ℕ) < r))).length
        = ((List.finRange t).filter (fun c : Fin t => decide ((c : ℕ) < r))).length
          + (if t < r then 1 else 0) := by
    simp [hs, List.filter_append, List.length_append, hmap, hlast]

  -- min の場合分けで閉じる
  by_cases htr : t < r
  · -- t < r のとき：min r t = t、min r (t+1) = t+1
    have : Nat.min r (t+1) = Nat.min r t + 1 := by
      have : Nat.min r t = t := by
        exact Nat.min_eq_right (Nat.le_of_lt htr)
      rw [this]
      have : Nat.min r (t+1) = t + 1 := by
        have : t + 1 ≤ r := Nat.succ_le_of_lt htr
        exact Nat.min_eq_right this
      rw [this]
    simpa [ih, this, htr, Nat.succ_eq_add_one,Nat.min_eq_left (Nat.le_of_lt htr)] using step
  · -- r ≤ t のとき：増分 0、min も据え置き
    have hle : r ≤ t := Nat.le_of_not_lt htr
    have : Nat.min r (t+1) = Nat.min r t := by
      simp [Nat.min_eq_left hle]
      simp [Nat.le_trans hle (Nat.le_succ t)]
    simpa [ih, this, htr, Nat.min_eq_left hle] using step


lemma filterLength (t r : ℕ) (hr : r < t) :
  ((List.finRange t).filter (fun c : Fin t => decide (r ≤ c))).length = t - r := by
  classical
  let p : Fin t → Bool := fun c => decide ((c : ℕ) < r)
  let q : Fin t → Bool := fun c => decide (r ≤ (c : ℕ))
  let pr := (List.finRange t).partition p
  have h₁ : pr.fst ++ pr.snd = List.finRange t := finRange_partition_lt_append t r
  have filter_decompose :
    (List.finRange t).filter q = (pr.fst.filter q) ++ (pr.snd.filter q) := by
    rw [←List.filter_append, h₁]
  have length_append :
    ((List.finRange t).filter q).length
      = (pr.fst.filter q).length + (pr.snd.filter q).length := by
    rw [filter_decompose, List.length_append]
  have pr_fst_nil :
    (pr.fst.filter q).length = 0 := by
    -- pr.fst のすべての要素 c は c < r を満たすので q c = decide (r ≤ c) = false
    apply List.length_eq_zero_iff.2
    apply List.filter_eq_nil_iff.2
    intro x hx
    have hx' : x ∈ (List.finRange t).filter p := by
      simpa [pr, List.partition_eq_filter_filter] using hx
    have hxP : p x = true := (List.mem_filter.mp hx').2
    have hx_lt_r : (x : ℕ) < r := by
      dsimp [p] at hxP
      exact of_decide_eq_true hxP
    have hq : q x = false := by
      dsimp [q]
      exact (decide_eq_false_iff_not).2 (Nat.not_le.mpr hx_lt_r)
    simp [hq]

  have filter_q_prsnd_eq : pr.snd.filter q = pr.snd := by
    apply List.filter_eq_self.2
    intro x hx
    -- x ∈ pr.snd から p x = false を取り出す
    have hx' : x ∈ (List.finRange t).filter (fun c => ! p c) := by
      -- pr = partition p (finRange t)
      simpa [pr, List.partition_eq_filter_filter] using hx

    have hx_not_p : !(p x) = true := by
      simp [List.mem_filter.mp hx']
    -- p x = false に変換
    have hx_p_false : p x = false := by
      cases hpx : p x <;> simp [hpx] at hx_not_p
      · exact rfl            -- p x = false の場合はそのまま

    -- ここから r ≤ x
    have hx_le : r ≤ (x : ℕ) := by
      dsimp [p] at hx_p_false
      -- decide ((x:ℕ) < r) = false  →  ¬ ((x:ℕ) < r)
      have : ¬ ((x : ℕ) < r) := by
        simpa [decide_eq_true_eq, decide_eq_false_iff_not] using hx_p_false
      exact Nat.le_of_not_lt this
    -- q x = true
    dsimp [q]
    simpa using hx_le

  -- pr.snd の長さを出すための和の等式
  have length_sum :
      pr.fst.length + pr.snd.length = t := by
    simpa using congrArg List.length h₁

  -- pr.fst の長さは r
  have pr_fst_len : pr.fst.length = r := by
    -- pr.fst = (finRange t).filter p
    have : ((List.finRange t).filter p).length = r := by
      have : r.min t = r := Nat.min_eq_left (Nat.le_of_lt hr)
      rw [<-this]
      simpa [p, Nat.min_eq_left hr] using length_filter_lt_finRange r t

    simpa [pr, List.partition_eq_filter_filter] using this

  -- 以上から pr.snd.length = t - r
  have pr_snd_len' : pr.snd.length = t - r := by
    -- Nat の等式から差を取り出す
    have := length_sum
    -- t = pr.fst.length + pr.snd.length かつ pr_fst_len = r
    -- → pr.snd.length = t - r
    simp [pr_fst_len] at this

    have h := congrArg (fun n => n - r) this
    -- h : (r + pr.snd.length) - r = t - r
    -- 左辺を簡約：r + n - r = n
    simpa [Nat.add_sub_cancel] using h


  -- 仕上げ：filter を外す
  have pr_snd_len :
      (pr.snd.filter q).length = t - r := by
    simpa [filter_q_prsnd_eq] using pr_snd_len'

  rw [length_append, pr_fst_nil, Nat.zero_add, pr_snd_len]

-- 各行（内側）の foldr 初期値 acc を [] にずらし、最後に ++ acc に出す補題
private lemma foldr_cons_if_push_append
  {α β : Type _} (xs : List α) (acc : List β)
  (p : α → Prop) [DecidablePred p] (f : (a : α) → p a → β) :
  xs.foldr (fun a acc' => if h : p a then f a h :: acc' else acc') acc
  = (xs.foldr (fun a acc' => if h : p a then f a h :: acc' else acc') []) ++ acc := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a
      · simp [List.foldr, h, ih, List.cons_append]
      · simp [List.foldr, h, ih]

-- 形式を整える補題
lemma foldr_push_general (t : ℕ) (L : List (Fin t)) :
    L.foldr
      (fun r acc =>
        (List.finRange t).foldr
          (fun c acc' =>
            if h : r ≤ c then (⟨(r,c), by simpa using h⟩) :: acc'
            else acc')
          acc)
      ([] : List { rc : Fin t × Fin t // rc.1 ≤ rc.2 })
  =
    L.foldr
      (fun r acc =>
        ((List.finRange t).foldr
          (fun c acc' =>
            if h : r ≤ c then (⟨(r,c), by simpa using h⟩) :: acc'
            else acc')
          [])
        ++ acc)
      [] := by
  induction L with
  | nil => simp
  | cons r rs ih =>
      rw [List.foldr_cons, List.foldr_cons]
      set A := List.foldr
        (fun r₁ acc =>
          (List.finRange t).foldr
            (fun c acc' =>
              if h : r₁ ≤ c then (⟨(r₁,c), by simpa using h⟩ : { rc : Fin t × Fin t // rc.1 ≤ rc.2 }) :: acc'
              else acc')
            acc)
        [] rs
      have hrow := foldr_cons_if_push_append
        (xs := List.finRange t) (acc := A)
        (p := fun c => r ≤ c)
        (f := fun c h => (⟨(r,c), by simpa using h⟩ : { rc : Fin t × Fin t // rc.1 ≤ rc.2 }))
      rw [hrow, ih]

-- if で cons するかしないかの形を filterMap に変える補題
lemma foldr_if_cons_eq_filterMap {α β : Type _}
  (xs : List α) (p : α → Prop) [DecidablePred p] (f : (a : α) → (p a → β)) :
  xs.foldr (fun a acc => if h : p a then f a h :: acc else acc) [] =
  xs.filterMap (fun a => if h : p a then some (f a h) else none) := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      simp [List.foldr, List.filterMap, ih]
      split <;> simp

lemma Nat.add_sub_comm (a b c : ℕ) (h : c ≤ a) : (a + b) - c = (a - c) + b := by
  rw [add_comm a b, add_comm (a - c) b]
  exact Nat.add_sub_assoc (n := b) (m := a) (k := c) (h := h)

lemma sum_reflect_rewrite (t : ℕ) :
    ∑ i ∈ Finset.range t, (t - i) = ∑ i ∈ Finset.range t, (t - 1 - i + 1) := by
  classical
  -- 同じ集合 `range t` 上で各 i について被加数を書き換える
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hit : i < t := Finset.mem_range.1 hi
  have hle' : i ≤ t - 1 := Nat.le_pred_of_lt hit
  have hle : i ≤ t := Nat.le_of_lt hit
  have htpos : 0 < t := Nat.lt_of_le_of_lt (Nat.zero_le i) hit
  have heq : t = (t - 1) + 1 := by
    have := Nat.succ_pred_eq_of_pos htpos
    -- t = succ (pred (t)) これは simpa でよい
    simpa using this.symm
  -- `t ≠ 0` は i < t から自動的に言えるので、`succ (t-1) = t`
  have hsub : t - i = (t - 1 - i) + 1 := by
    have hL : t - i = (t - 1 + 1) - i := congrArg (fun x => x - i) heq
    -- t を (t-1) + 1 に置き換え
    rw [hL]
    exact Nat.add_sub_comm (a := t - 1) (b := 1) (c := i) (h := hle')

  exact hsub

lemma sum_range_t_minus (t : ℕ) :
  ∑ i ∈ Finset.range t, (t - i) = ∑ i ∈ Finset.range t, (i + 1) := by
  classical
  -- まず被加数を書き換えて反射形に合わせる
  have h₁ := sum_reflect_rewrite t
  -- 反射補題を当てる（`f i = i+1`）
  have h₂ := Finset.sum_range_reflect (f := fun i => i + 1) (n := t)
  -- 連結
  exact h₁.trans h₂

/- Finset.range について Σ i ∈ Finset.range t, (t-i) = t * (t+1) / 2 を証明 -/
lemma finset_sum_sub_range (t : ℕ) :
    ∑ i ∈ Finset.range t, (t - i) = t * (t + 1) / 2 := by
  classical
  -- 反射： i ↦ (t-1-i)
  have hreflect :
      (∑ i ∈ Finset.range t, (t - i)) = (∑ i ∈ Finset.range t, (i + 1)) :=
    sum_range_t_minus t
  -- 左辺を「定数和 + 身元の和」に分解
  have hsplit :
      (∑ i ∈ Finset.range t, (i + 1))
      = (∑ i ∈ Finset.range t, i) + Finset.card (Finset.range t) := by
    -- `sum_add_distrib` と `sum_const_nat`
    simp [Finset.sum_add_distrib,Finset.card_range,Nat.add_comm]
  -- ∑ i = t*(t-1)/2
  have htri : (∑ i ∈ Finset.range t, i) = t * (t - 1) / 2 := by
    simpa using Finset.sum_range_id (n := t)
  -- (3) 算術： (t*(t-1)/2) + t = t*(t+1)/2
  have hcalc : (t * (t - 1) / 2 + t : ℕ) = t * (t + 1) / 2 := by
    -- (a + b*c)/c = a/c + b （c ≠ 0）を a=t*(t-1), b=t, c=2 に適用
    have hx :
        t * (t - 1) / 2 + t
        = (t * (t - 1) + t * 2) / 2 := by
      -- 右向きにしたいので .symm を使う
      -- まず c=2 > 0 を用意
      have hc : 0 < 2 := by decide
      simpa using (Nat.add_mul_div_right (t * (t - 1)) t hc).symm
    -- 分子の恒等式 t(t-1) + 2t = t(t+1) を /2 に持ち上げる
    have hr :
        (t * (t - 1) + t * 2) / 2 = (t * (t + 1)) / 2 := by
      have : t * (t - 1) + t * 2 = t * (t + 1) := by
        -- t で場合分け（t=0 のときは自明、t=succ n なら (n+1)*n + (n+1)*2 = (n+1)*(n+2)）
        cases t with
        | zero =>
            simp
        | succ n =>
            -- 目標は (n+1)*n + (n+1)*2 = (n+1)*(n+2)
            -- 左を右へ「因数分解」するには mul_add を対称に使う
            -- mul_add : m*(a+b) = m*a + m*b なので、その対称を `simpa` で
            simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
              using (Nat.mul_add (n+1) n 2).symm
      simp [this]
    simp [hx, hr]

  -- まとめ： (t*(t-1)/2) + t = t*(t+1)/2
  have : (∑ i ∈ Finset.range t, (i + 1)) = t * (t + 1) / 2 := by
    simp [hsplit, htri, hcalc]

  -- 反射で戻す
  simpa [hreflect] using this

/- `finRange` を `range` に落とす（値を取り出すだけ） -/
private lemma finRange_map_val (t : ℕ) :
  (List.finRange t).map (fun a : Fin t => (a : ℕ)) = List.range t := by
  classical
  -- get? ベースで ext するのが安定
  have hlen :
      ((List.finRange t).map (fun a : Fin t => (a : ℕ))).length
      = (List.range t).length := by simp
  apply List.ext_getElem hlen
  intro i hi hi'
  have hi_fin : i < (List.finRange t).length := by simpa using hi
  simp

/- 上三角の個数は `t(t+1)/2`。 -/
lemma upperPairsLength (t : ℕ) :
  (upperPairs t).length = t * (t + 1) / 2 := by
  classical
  -- `upperPairs` の定義を展開
  unfold upperPairs
  -- 2) 各行の foldr 初期値を [] に押し出して、最後に ++ acc にする
  have hpush :
    List.foldr
      (fun r acc =>
        (List.finRange t).foldr
          (fun c acc' =>
            if h: r ≤ c then ⟨(r, c), by simpa using h⟩ :: acc'
            else acc')
          acc
        )
      ([] : List { rc : Fin t × Fin t // rc.1 ≤ rc.2 })
      (List.finRange t)
    =
    List.foldr
      (fun r acc =>
        ((List.finRange t).foldr
          (fun c acc' =>
            if h : r ≤ c then ⟨(r, c), by simpa using h⟩ :: acc'
            else acc')
          []) ++ acc)
      [] (List.finRange t) := foldr_push_general t (List.finRange t)
  -- flatMap, filterMap の形に変形して補題が使える形にする。
  have hsum :
    (List.finRange t).foldr
      (fun r acc =>
        ((List.finRange t).foldr
          (fun c acc' =>
            if h : r ≤ c then ⟨(r, c), by simpa using h⟩ :: acc' else acc')
          []) ++ acc)
      ([] : List {rc : Fin t × Fin t // rc.1 ≤ rc.2}) =
    (List.finRange t).flatMap
      (fun r =>
        (List.finRange t).filterMap (fun c =>
          if h : r ≤ c
          then some ⟨(r, c), by simpa using h⟩
          else none)) := by
      simp[List.flatMap_eq_foldl, List.append_nil]
      ext r
      simp [foldr_if_cons_eq_filterMap]
  rw [hpush, hsum]
  -- 長さの和を sum に変える
  simp [List.length_flatMap]

  -- 行 r の長さを数えるコア部分
  have rowLen (r : Fin t) :
    ((List.finRange t).filterMap
      (fun c : Fin t => if h : r ≤ c then some (⟨(r,c), by simpa using h⟩
          : { rc : Fin t × Fin t // rc.1 ≤ rc.2 }) else none)).length
    = t - (r : ℕ) := by
    classical
    -- filterMap → countP
    have h₁ :
      ((List.finRange t).filterMap
        (fun c : Fin t => if h : r ≤ c then some (⟨(r,c), by simpa using h⟩
          : { rc // rc.1 ≤ rc.2 }) else none)).length
      =
      List.countP
        (fun c : Fin t =>
          (if h : r ≤ c then some (⟨(r,c), by simpa using h⟩
            : { rc // rc.1 ≤ rc.2 }) else none).isSome)
        (List.finRange t) := by
      simp [List.length_filterMap_eq_countP]
    -- isSome 簡約 → decide へ
    have hpred :
      (fun c : Fin t =>
        (if h : r ≤ c then some (⟨(r,c), by simpa using h⟩
          : { rc // rc.1 ≤ rc.2 }) else none).isSome)
      =
      (fun c : Fin t => decide (r ≤ c)) := by
      funext c; by_cases h : r ≤ c <;> simp [h]
    -- countP → length(filter)
    have h₂ :
      List.countP (fun c : Fin t => decide (r ≤ c)) (List.finRange t)
      =
      ((List.finRange t).filter (fun c : Fin t => decide (r ≤ c))).length := by
      simp [List.countP_eq_length_filter]
    -- ここから整数側へ：長さ = t - r
    have hlen :
      ((List.finRange t).filter (fun c : Fin t => decide (r ≤ c))).length
      = t - (r : ℕ) := filterLength t r (Nat.lt_of_le_of_lt (Nat.le_of_eq (rfl)) r.is_lt)

    simpa [h₁, hpred, h₂] using hlen

  -- 行ごとの長さ関数
  let f : Fin t → ℕ :=
    fun a =>
      (List.filterMap
        (fun c : Fin t =>
          if h : a ≤ c then
            some (⟨(a, c), by simpa using h⟩ :
              { rc : Fin t × Fin t // rc.1 ≤ rc.2 })
          else none)
        (List.finRange t)).length

  -- 目標の簡単な形
  let g : Fin t → ℕ := fun a => t - (a : ℕ)

  -- map の中身を “各 a で” rowLen で置換
  have h_congr :
    ∀ a ∈ (List.finRange t),
      f a = g a := by
    intro a ha
    -- rowLen a : … = t - (a : ℕ)
    -- f, g の定義を展開して一致させるだけ
    simpa [f, g] using rowLen a

  have hrows :
    (List.map f (List.finRange t)) =
    (List.map g (List.finRange t)) := by
    exact List.map_congr_left (l := List.finRange t) h_congr

  -- 和に持ち上げ（両辺に sum を適用）
  have hsum_rows :
    ((List.map f (List.finRange t)).sum) =
    ((List.map g (List.finRange t)).sum) :=
    congrArg List.sum hrows

  rw [hsum_rows]
  simp [g]
  trace_state
  have : ((List.finRange t).map (fun a : Fin t => t - (a : ℕ))).sum =
    ∑ i ∈ Finset.range t, (t - i) := by
    have hofFn_eq : (List.finRange t).map (fun a : Fin t => t - (a : ℕ))
      = List.ofFn (fun i : Fin t => t - (i : ℕ)):= by
      simp [List.ofFn_eq_map]
    simp [hofFn_eq, Fin.sum_ofFn, Finset.sum_range]

  simp [this, finset_sum_sub_range]

/- 係数環を多相化した構成。 -/
namespace PolyOver

variable (P : Params) {R : Type*} [CommSemiring R]

/- p_i = (X_(i,0), ..., X_(i,t-1)) over R -/
noncomputable def pVecR (i : Fin P.n) :
    Vector (MvPolynomial (Var P) R) P.t :=
  Vector.ofFn (fun a : Fin P.t => MvPolynomial.X (i, a))

/- S_uv の (r,c) 成分 = p_u[r]*p_v[c] + p_v[r]*p_u[c] over R -/
noncomputable def symOuterEntryR
  (u v : Fin P.n) (r c : Fin P.t) :
  MvPolynomial (Var P) R :=
  (pVecR P (R:=R) u).get r * (pVecR P (R:=R) v).get c +
  (pVecR P (R:=R) v).get r * (pVecR P (R:=R) u).get c

/- φ(e) を上三角順で並べた List 版 over R -/
noncomputable def phiListR (e : Ground P) :
    List (MvPolynomial (Var P) R) := by
  classical
  -- 代表 (u,v) を取り出す
  let p : (Fin P.n × Fin P.n) := Classical.choose (Quot.exists_rep e)
  have hp : Quot.mk (Sym2.Rel (Fin P.n)) p = e :=
    Classical.choose_spec (Quot.exists_rep e)
  let u : Fin P.n := p.1
  let v : Fin P.n := p.2
  -- 上三角を列挙
  exact (upperPairs P.t).map (fun ⟨⟨r,c⟩, _⟩ =>
    symOuterEntryR P (R:=R) u v r c)

/- φ(e) のベクトル版（長さ d_col） over R -/
noncomputable def phiR (e : Ground P) :
    Vector (MvPolynomial (Var P) R) (d_col P) := by
  classical
  let xs := phiListR P (R:=R) e
  -- まず phiListR の長さを直接示す
  have hx0 : (phiListR P (R:=R) e).length = d_col P := by
    -- map の長さ = 元リストの長さ、に落として upperPairsLength を使う
    simpa [phiListR, List.length_map, d_col] using upperPairsLength P.t
  -- それを xs に転写
  have hx : xs.length = d_col P := by
    simpa [xs] using hx0
  -- 以降は hx を使って Vector.cast
  exact Vector.cast hx (Vector.ofFn (fun i => xs.get i))


/- 構成行列（行 d_col、列 Ground） over R -/
noncomputable def M_polyR :
  Matrix (Fin (d_col P)) (Ground P) (MvPolynomial (Var P) R) :=
  fun r e => (phiR P (R:=R) e).get r

end PolyOver

/- 厳密フェーズ（係数 ℚ） -/
noncomputable def M_polyQ (P : Params) :
  Matrix (Fin (d_col P)) (Ground P) (MvPolynomial (Var P) ℚ) :=
  PolyOver.M_polyR P (R:=ℚ)

/- 乱択フェーズ（係数 ℤ） -/
noncomputable def M_polyZ (P : Params) :
  Matrix (Fin (d_col P)) (Ground P) (MvPolynomial (Var P) Int) :=
  PolyOver.M_polyR P (R:=Int)

/- 既存の ℚ 係数版（Kpoly = ℚ）を引き続き使いたい場合はそのままでOK。
  VG なども M_polyQ を参照するようにすると統一できます。 -/
noncomputable def VG (G : Instance) :
  Matrix (Fin (d_col G.P)) (Fin G.edgesList.length) (Kpoly G.P) :=
  fun r c => (M_polyQ G.P) r (G.edgesList.get c)


/- 線形マトロイドの基本的な定義から独立性や閉包などを抽出 -/

namespace LM

open Matrix

variable {K : Type*} [Field K]
variable {β : Type*} [Fintype β] [DecidableEq β]
variable {d : ℕ}

/- 列ベクトル族 -/
def colsFamily (M : Matrix (Fin d) β K) : β → (Fin d → K) :=
  fun j i => M i j

/- 全列独立 -/
def AllColsIndependent (M : Matrix (Fin d) β K) : Prop :=
  LinearIndependent K (colsFamily M)

/- 部分集合 S 上の列独立 -/
def ColsIndependentOn (M : Matrix (Fin d) β K)
    (S : Finset β) : Prop :=
  LinearIndependent K (fun j : {j // j ∈ S} => colsFamily M j)

/- サーキット（極小従属） -/
def IsCircuit (M : Matrix (Fin d) β K)
    (C : Finset β) : Prop :=
  (¬ ColsIndependentOn M C) ∧
  ∀ f ∈ C, ColsIndependentOn M (C.erase f)

/- 列集合 S が張る部分空間 -/
def spanCols (M : Matrix (Fin d) β K)
    (S : Finset β) : Submodule K (Fin d → K) :=
  Submodule.span K (Set.range (fun j : {j // j ∈ S} => colsFamily M j))

/- 閉包（span が増えない列の集合） -/
def Closure (M : Matrix (Fin d) β K)
    (C : Finset β) : Set β :=
  { e | spanCols M (C ∪ {e}) = spanCols M C }

/- `Params` 版の構成行列（係数は分数体 `FractionRing (MvPolynomial …)`）。 -/
noncomputable def M (P : Params) :
  Matrix (Fin (d_col P)) (Ground P) (FractionRing (MvPolynomial (Var P) ℚ)) :=
  fun r e =>
    algebraMap (MvPolynomial (Var P) ℚ)
               (FractionRing (MvPolynomial (Var P) ℚ))
               (M_polyQ P r e)

end LM

namespace St
open LM

/- S_t の構成行列（分数体上；Params 版）。 -/
noncomputable def M (P : Params) :
  Matrix (Fin (d_col P)) (Ground P)
         (FractionRing (MvPolynomial (Var P) ℚ)) :=
  LM.M P

/- S_t-独立（列集合 S の独立；Params 版）。 -/
def indep (P : Params) (S : Finset (Ground P)) : Prop :=
  LM.ColsIndependentOn (M := M P) S

/- S_t-サーキット（極小従属；Params 版）。 -/
def isCircuit (P : Params) (C : Finset (Ground P)) : Prop :=
  LM.IsCircuit (M := M P) C

/- S_t-閉包（Set 版；Params 版）。 -/
def closureSet (P : Params) (C : Finset (Ground P)) : Set (Ground P) :=
  LM.Closure (M := M P) C

/- S_t-閉包（Finset 版；Params 版）。 -/
noncomputable def closure (P : Params) (C : Finset (Ground P)) : Finset (Ground P) := by
  classical
  -- `Set.toFinset : Set α → Finset α` は `[Fintype α]` と「メンバーシップ可決定」があれば使える
  exact (closureSet P C).toFinset

/- 全列（=全辺）独立／従属（Params 版）。 -/
abbrev indepAll (P : Params) : Prop := indep P Finset.univ
abbrev depAll (P : Params) : Prop := ¬ indepAll P

/- 独立の一致（LM 汎用定義との一致；Params 版）。 -/
theorem colsIndependentOn_iff_LM
  (P : Params) (S : Finset (Ground P)) :
  LM.ColsIndependentOn (M := LM.M P) S ↔ indep P S := by
  rfl

/- サーキットの一致（LM 汎用定義との一致；Params 版）。 -/
theorem circuit_iff_LM
  (P : Params) (C : Finset (Ground P)) :
  LM.IsCircuit (M := LM.M P) C ↔ isCircuit P C := by
  rfl

/- 閉包の一致（LM 汎用定義との一致；Params 版）。 -/
theorem closure_eq_LM
  (P : Params) (C : Finset (Ground P)) :
  LM.Closure (M := LM.M P) C = closureSet P C := by
  rfl

end St


namespace Cnt
open LM St

/- 固定パラメータ `P` のもとでの「グラフ」＝ `K_n` の辺集合 `Ground P` の有限部分集合。 -/
abbrev Graph (P : Params) := Finset (Ground P)

/- 「G が 𝒞_{n,t} に属する」述語（定義は後で具体化）。 -/
def InCnt (P : Params) (F : Graph P) : Prop := sorry

/- 付録Bの帰納定義で与える重み `c_t`（`Ground P` の部分集合上に定義）。 -/
def c_t (P : Params) (F : Graph P) : ℕ := sorry

/- `rank_{S_t}(F)`：`S_t` の構成行列を `F` 列に制限したときの列ランク。 -/
def rank_St (P : Params) (F : Graph P) : ℕ := sorry

/- 「部分グラフ」＝包含。 -/
def Subgraph (P : Params) (H G : Graph P) : Prop := H ⊆ G

/- `H` が `F` に同型に埋め込める（Kn 上の頂点置換を許すイメージ；型だけ先に）。 -/
def EmbedsIso (P : Params) (H F : Graph P) : Prop := sorry

/- `C_t`-independent（論文の定義を Kn=固定地集合 上に移植）。 -/
def CtIndependent (P : Params) (G : Graph P) : Prop :=
  ∀ ⦃H F : Graph P⦄, Subgraph P H G → InCnt P F → EmbedsIso P H F → H.card ≤ c_t P F

def CtDependent (P : Params) (G : Graph P) : Prop := ¬ CtIndependent P G

/- `S_t`-independent / -dependent（`S_t` マトロイドの独立をそのまま使う）。 -/
abbrev StIndependent (P : Params) (G : Graph P) : Prop := St.indep P G
abbrev StDependent (P : Params) (G : Graph P) : Prop := ¬ St.indep P G

/- 将来の整合：ランクによる判定との同値（型だけ先に）。 -/
-- TODO: 証明を書く
axiom StDependent_iff_rank (P : Params) (G : Graph P) :
  StDependent P G ↔ rank_St P G < G.card

/- 反例：`C_t`-independent かつ `S_t`-dependent。 -/
def Counterexample (P : Params) (G : Graph P) : Prop :=
  CtIndependent P G ∧ StDependent P G

def ExistsCounterexample (P : Params) : Prop :=
  ∃ G : Graph P, Counterexample P G

end Cnt


namespace Checker
open scoped BigOperators
open LM St

-- echelon form の定義

/- REF のメタデータ：ピボット行数 r と、各 i < r のピボット列 pivot i -/
structure REFMeta (m n : Nat) where
  (r : Nat)
  (hr : r ≤ m)                 -- 非零行数 r ≤ m
  (pivot : Fin r → Fin n)
  (strictMono : StrictMono pivot)   -- ピボット列が増加
/- A が「REFMeta による REF」 -/
def IsREF {K} {m n : ℕ} [Field K] (A : Matrix (Fin m) (Fin n) K) (ref_meta : REFMeta m n) : Prop :=
  let r := ref_meta.r; let p := ref_meta.pivot;
  -- 1) 非零行は 0..r-1、r..m-1 は全零
  (∀ i : Fin r, A (Fin.castLE ref_meta.hr i) (p i) = 1)
  ∧ (∀ {i : Fin m}, ∀ j, (i < r) ∨  A i j = 0)
  -- 2) ピボット列の他行は 0
  ∧ (∀ {i : Fin m} {k : Fin r}, i ≠ (Fin.castLE ref_meta.hr k) → A i (p k) = 0)
  -- 3) 各ピボットの左側は 0
  ∧ (∀ {i : Fin r} {j : Fin n}, (j : Nat) < (p i).val → A (Fin.castLE ref_meta.hr i) j = 0)
  -- 4) ピボット列は増加
  ∧ (∀ i j, i < j → (p i).val < (p j).val)

/- `LM.M P` の列を有限集合 `G`（辺集合）で制限した部分行列。 -/
noncomputable def restrictCols
  (P : Params) (G : Finset (Ground P)) :
  Matrix (Fin (d_col P)) {e : Ground P // e ∈ G}
          (FractionRing (MvPolynomial (Var P) ℚ)) :=
  fun r c => (LM.M P) r c.1

/-======================= 乱択フェーズ (ZMod p) =======================-/

variable {p : Nat} [hp : Fact (Nat.Prime p)]
local notation "𝔽p" => ZMod p

/- ℚ → 𝔽p への係数写像（分母が p と互いに素であることを仮定）。
    あなたの行列は係数 1 だけなので実運用では常に安全。 -/
noncomputable def ratToZMod (q : ℚ) : 𝔽p :=
  let num : ℤ := q.num
  let den : ℕ := q.den
  -- 係数が 1 の場合は den=1。一般に den ∤ p を仮定：den⁻¹ が存在
  (ZMod.cast (n := p) num) * (ZMod.cast (n := p) den)⁻¹


/- 多変数多項式（係数 ℤ）を 𝔽p に評価する。 -/
noncomputable def evalPolyZMod
  {s : Nat}
  (α : Fin s → ZMod p)
  : MvPolynomial (Fin s) Int →+* 𝔽p :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod p)) α

/- A : Matrix (Fin d) (Fin m) (MvPolynomial … ℤ) を 𝔽p のランダム点 α で評価。 -/
noncomputable def evalMatrixZMod
  {d m s : Nat}
  (A : Matrix (Fin d) (Fin m) (MvPolynomial (Fin s) ℤ))
  (α : Fin s → 𝔽p) :
  Matrix (Fin d) (Fin m) 𝔽p :=
  fun i j =>
    -- 係数が整数しか出ない構成なら、`Int.castRingHom` でも可：
    -- MvPolynomial.eval₂Hom (Int.castRingHom _) α (A i j)
    evalPolyZMod α (A i j)


/- 「A は各行の長さが常に n」の長方形性 -/
def Rect {α : Type*} (A : Array (Array α)) (n : Nat) : Prop :=
  ∀ i (hi : i < A.size), (A[i]).size = n

/- 長方形性の証明つきに Matrix へ（Inhabited 不要・`!` 不要） -/
def toMat {α : Type*}
  (A : Array (Array α)) (m n : Nat)
  (hrows : A.size = m) (hrect : Rect A n) :
  Matrix (Fin m) (Fin n) α :=
  fun ⟨i, hi⟩ ⟨j, hj⟩ =>
    -- i を A.size にキャストして安全にアクセス
    let hiA : i < A.size := by simpa [hrows] using hi
    let row := A[i]
    have hrowlen : row.size = n := by
      simpa [row] using hrect i hiA
    have hj' : j < row.size := by
      simpa [hrowlen] using hj
    row[j]

def toArray2D {m n} {α : Type*} (M : Matrix (Fin m) (Fin n) α) :
  Array (Array α) :=
  Array.ofFn (fun i => Array.ofFn (fun j => M i j))

/- `toArray2D` の行数（外側サイズ） -/
lemma toArray2D_rowSize {m n} {K} (M : Matrix (Fin m) (Fin n) K) :
  (toArray2D M).size = m := by
  -- `Array.ofFn` のサイズ性質
  simp [toArray2D]

/- `toArray2D` は長方形（各行の長さ n） -/
lemma toArray2D_rect {m n} {K} (M : Matrix (Fin m) (Fin n) K) :
  Rect (toArray2D M) n := by
  simp [Rect, toArray2D]

/- i行とj行を入れ替える。範囲外が混じる場合は何もしない。 -/
@[inline] def swapRows {α} (i j : Nat) (A : Array (Array α)) : Array (Array α) :=
  if h : i < A.size ∧ j < A.size then
    let ri := A[i]
    let rj := A[j]
    (A.set! i rj).set! j ri
  else
    A

/- 行iをスカラーk倍にする（Kは体）。範囲外なら何もしない。 -/
@[inline] def rowScale {K} [Field K] (i : Nat) (k : K)
    (A : Array (Array K)) : Array (Array K) :=
  if hi : i < A.size then
    let row := A[i]
    -- 全要素に k を掛けるだけ（Array.map を使うと簡潔）
    let newRow := row.map (fun x => k * x)
    A.set! i newRow
  else
    A

/- 行i ← 行i + α・行k（axpy）。どちらかが範囲外なら何もしない。 -/
@[inline] def rowAxpy {K} [Field K] (i k : Nat) (α : K) (A : Array (Array K))
  (n : Nat) (hrect : Rect A n) : Array (Array K) :=
  if hik : i < A.size ∧ k < A.size then
    let ri := A[i]; let rk := A[k]
    have hri : ri.size = n := hrect i hik.left
    have hrk : rk.size = n := hrect k hik.right
    -- 安全：長さ n の配列を Fin n で初期化
    let newRow : Array K :=
      Array.ofFn (fun j : Fin n => ri[j] + α * rk[j])
    A.set! i newRow
  else
    A

/- 基本変形後も rect が保持される補題 -/
lemma preserve_rowSize_swapRows
  {m α}
  (A : Array (Array α)) (hAsize : A.size = m)
  (i j : ℕ) (hi : i < m) (hj : j < m) :
  (swapRows i j A).size = m := by
    simp [swapRows, hAsize]
    have h : i < m ∧ j < m := by simp [hi, hj]
    simp [h, hAsize]

lemma preserve_rect_swapRows
  {m n} {α : Type u} [Field α]
  (A : Array (Array α)) (hAsize : A.size = m) (hrectA : Rect A n)
  (i j : ℕ) (hi : i < m) (hj : j < m) :
  Rect (swapRows i j A) n := by
    have h : i < A.size ∧ j < A.size := by rw [hAsize]; simp [hi, hj]
    simp [swapRows, h, Array.setIfInBounds]
    intro k hk
    simp [Array.getElem_set]
    by_cases hkj : k = j
    · simp [Eq.symm hkj, hrectA i]
    · simp [ne_comm.mp hkj]
      by_cases hki : k = i
      · simp [Eq.symm hki, hrectA j]
      · simp [ne_comm.mp hki, hrectA k]

lemma swapRows_size
  {α} (A : Array (Array α)) {i j : Nat} :
  (swapRows i j A).size = A.size := by
  -- i または j が範囲外の場合
  by_cases h : i < A.size ∧ j < A.size
  · simp [swapRows, h]
  · simp [swapRows, h]

lemma swapRows_get_left
  {α} (A : Array (Array α)) {i j : Nat}
  (hi : i < A.size) (hj : j < A.size) :
  (swapRows i j A)[i]'(
    by
      simp [swapRows, hi, hj]
  ) = A[j] := by
  -- i, j ともに範囲内
  have h : i < A.size ∧ j < A.size := ⟨hi, hj⟩
  simp [swapRows, h, Array.setIfInBounds]
  by_cases hji : i = j
  · simp [Eq.symm hji]
  · have hji' : i ≠ j := by
      intro hij
      contradiction
    conv =>
      lhs
      rw [Array.getElem_set]
    simp [ne_comm.mp hji']

lemma swapRows_get_right
  {α} (A : Array (Array α)) {i j : Nat}
  (hi : i < A.size) (hj : j < A.size) :
  (swapRows i j A)[j]'(
    by
      simp [swapRows, hi, hj]
  ) = A[i] := by
  -- i, j ともに範囲内
  have h : i < A.size ∧ j < A.size := ⟨hi, hj⟩
  simp [swapRows, h, Array.setIfInBounds]

lemma preserve_rowSize_rowScale
  {m α} [Field α]
  (A : Array (Array α)) (hAsize : A.size = m)
  (i : ℕ) (k : α) (hi : i < m) :
  (rowScale i k A).size = m := by
    simp [rowScale, hAsize]
    have hi' : i < m := by simp [hi]
    simp [hi', hAsize]

lemma preserve_rect_rowScale
  {m n α} [Field α]
  (A : Array (Array α)) (hAsize : A.size = m) (hrectA : Rect A n)
  (i : ℕ) (k : α) (hi : i < m) :
  Rect (rowScale i k A) n := by
    have hi' : i < A.size := by rw [hAsize]; simp [hi]
    simp [rowScale, hi', Array.setIfInBounds]
    intro j hj
    simp [Array.getElem_set]
    by_cases hj' : j = i
    · simp [Eq.symm hj', hrectA j]
    · simp [ne_comm.mp hj', hrectA j]

lemma preserve_rowSize_rowAxpy
  {m n α} [Field α]
  (A : Array (Array α)) (hAsize : A.size = m)
  (i k : ℕ) (α : α)
  (hi : i < m) (hk : k < m) (hrect : Rect A n) :
  (rowAxpy i k α A n hrect).size = m := by
    simp [rowAxpy, hAsize]
    have h : i < m ∧ k < m := by simp [hi, hk]
    simp [h, hAsize]

lemma preserve_rect_rowAxpy
  {m n α} [Field α]
  (A : Array (Array α)) (hAsize : A.size = m) (hrectA : Rect A n)
  (i k : ℕ) (α : α)
  (hi : i < m) (hk : k < m) :
  Rect (rowAxpy i k α A n hrectA) n := by
    have h : i < A.size ∧ k < A.size := by rw [hAsize]; simp [hi, hk]
    simp [rowAxpy, h, Array.setIfInBounds]
    intro k hk
    simp [Array.getElem_set]
    by_cases hki : k = i
    · simp [Eq.symm hki]
    · simp [ne_comm.mp hki, hrectA k]

/- 証明付きで基本変形を行う関数群 -/
structure Rectified (m n : Nat) (α : Type u) where
  A : Array (Array α)
  rowSize : A.size = m
  rect : Rect A n

/- いま注目している行列（配列→行列化） -/
@[inline] def matOf {m n K} [Field K] (R : Rectified m n K) : Matrix (Fin m) (Fin n) K :=
  toMat R.A m n R.rowSize R.rect

/- Matrix から `Rectified` を作る便利コンストラクタ -/
def rectifiedOfMatrix {m n} {K} (M : Matrix (Fin m) (Fin n) K) : Rectified m n K :=
{ A := toArray2D M
, rowSize := toArray2D_rowSize M
, rect := toArray2D_rect M }

/- 上の構成で `matOf` は元の `M` に戻る（往復整合性） -/
lemma matOf_rectifiedOfMatrix {m n} {K} [Field K]
  (M : Matrix (Fin m) (Fin n) K) :
  matOf (rectifiedOfMatrix (K:=K) M) = M := by
  -- `toMat (toArray2D M) ...` が pointwise に M と一致
  funext i j
  -- `toMat` の定義を展開して、`Array.ofFn` の定義で約束通り取り出せることを示す
  -- （あなたの `toMat` の補助等に合わせて `simp` ラインを調整）
  simp [rectifiedOfMatrix, toArray2D, matOf, toMat]

@[simp] lemma matOf_rectifiedOfMatrix_apply
  {m n K} [Field K] (M : Matrix (Fin m) (Fin n) K) (i : Fin m) (j : Fin n) :
  (matOf (rectifiedOfMatrix (K:=K) M)) i j = M i j := by
  simp [matOf_rectifiedOfMatrix (K:=K) M]

@[simp] lemma rowSize_rectifiedOfMatrix
  {m n K} (M : Matrix (Fin m) (Fin n) K) :
  (rectifiedOfMatrix (K:=K) M).A.size = m :=
  toArray2D_rowSize M


-- 行入替の保存：R ↦ R'
def rSwap {m n} {K : Type u} [Field K] (R : Rectified m n K) (i j : Nat) : Rectified m n K := by
  by_cases hij : i < R.A.size ∧ j < R.A.size
  · have hi' : i < m := by simpa [R.rowSize] using hij.left
    have hj' : j < m := by simpa [R.rowSize] using hij.right
    exact {
      A := swapRows i j R.A,
      rowSize := preserve_rowSize_swapRows R.A R.rowSize i j hi' hj',
      rect  := preserve_rect_swapRows R.A R.rowSize R.rect i j hi' hj'
    }
  · exact {
      A := swapRows i j R.A,
      rowSize := by simpa [swapRows, hij] using R.rowSize,
      rect  := by simpa [swapRows, hij] using R.rect
    }

def rScale {m n} {K : Type u} [Field K]
(R : Rectified m n K) (i : Nat) (k : K) : Rectified m n K := by
  by_cases hi : i < R.A.size
  · have hi' : i < m := by simpa [R.rowSize] using hi
    exact {
      A := rowScale i k R.A,
      rowSize := preserve_rowSize_rowScale R.A R.rowSize i k hi',
      rect  := preserve_rect_rowScale R.A R.rowSize R.rect i k hi'
    }
  · exact {
      A := rowScale i k R.A,
      rowSize := by simpa [rowScale, hi] using R.rowSize,
      rect  := by simpa [rowScale, hi] using R.rect
    }

def rAxpy {m n} {K : Type u} [Field K]
(R : Rectified m n K) (i k : Nat) (a : K) : Rectified m n K := by
  by_cases hik : i < R.A.size ∧ k < R.A.size
  · have hi' : i < m := by simpa [R.rowSize] using hik.left
    have hk' : k < m := by simpa [R.rowSize] using hik.right
    exact {
      A := rowAxpy i k a R.A n R.rect,
      rowSize := preserve_rowSize_rowAxpy R.A R.rowSize i k a hi' hk' R.rect,
      rect  := preserve_rect_rowAxpy R.A R.rowSize R.rect i k a hi' hk'
    }
  · exact {
      A := rowAxpy i k a R.A n R.rect,
      rowSize := by simpa [rowAxpy, hik] using R.rowSize,
      rect  := by simpa [rowAxpy, hik] using R.rect
    }

/-- pivot 行 `row` を使って、列 `col` を掃き出す内部ループ -/
def clearPivotCol_loop
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hcol : col < n) :
  Nat → Rectified m n K
| i =>
  if hi : i < m then
    let fi : Fin m := ⟨i, by simpa [R.rowSize] using hi⟩

    if hrow : i = row then
      -- pivot 行はそのままスキップ
      clearPivotCol_loop R row col hcol (i+1)
    else
      -- (i, col) 成分
      let hcol' : col < n := hcol
      let a : K := (matOf R) fi ⟨col, hcol'⟩
      let R' : Rectified m n K := rAxpy R i row (-a)
      clearPivotCol_loop R' row col hcol (i+1)
  else
    R
termination_by i => m - i

/-- pivot 行 `row` を使って、列 `col` を全て 0 にする（pivot 行以外） -/
def clearPivotCol
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hcol : col < n) :
  Rectified m n K :=
  clearPivotCol_loop R row col hcol 0

lemma preserve_rowSize_clearPivotCol_loop_aux
  {m n K} [Field K]
  (row col : Nat) (hcol : col < n) :
  ∀ k,                             -- ★ measure: k = m - i
    ∀ {i : Nat} (R : Rectified m n K),
      i ≤ m →
      m - i = k →
      (clearPivotCol_loop R row col hcol i).A.size = m := by
  intro k
  refine Nat.rec
    (motive := fun k =>
      ∀ {i : Nat} (R : Rectified m n K),
        i ≤ m → m - i = k →
        (clearPivotCol_loop R row col hcol i).A.size = m)
    ?base
    ?step
    k
  · -- base : k = 0
    -- ゴール：
    --   ∀ {i} (R : Rectified m n K),
    --     i ≤ m → m - i = 0 → size = m
    intro i R hi h_eq
    -- m - i = 0 かつ i ≤ m  ⇒ i = m
    have hmi_le : m ≤ i :=
      Nat.sub_eq_zero_iff_le.mp h_eq
    have h_eq_i : i = m := Nat.le_antisymm hi hmi_le

    -- i = m なら clearPivotCol_loop は hi : ¬ m < m で else 分岐に落ちて R を返す
    have : ¬ m < m := Nat.lt_irrefl _
    -- clearPivotCol_loop R row col hcol m = R
    have hR : (clearPivotCol_loop R row col hcol m) = R := by
      simp [clearPivotCol_loop]
    -- 行数は R の rowSize
    simpa [h_eq_i, hR] using R.rowSize
  · -- step : k → k.succ
    -- IH:
    --   ∀ {i} (R : Rectified m n K),
    --     i ≤ m → m - i = k → size = m
    intro k IH i R hi h_eq
    -- ここでゴールは
    --   m - i = k.succ という前提のもと、
    --   clearPivotCol_loop ... i の size = m を示すこと
    by_cases hi_lt : i < m
    · -- (1) i < m ならループ本体に入る
      have hi_succ_le : i.succ ≤ m := Nat.succ_le_of_lt hi_lt

      -- (2) m - i = k.succ から m - (i+1) = k を作る
      have hk_eq : m - (i+1) = k := by
        -- i ≤ m が欲しいので hi をそのまま使う
        have hi_le : i ≤ m := hi
        -- h_eq : m - i = k.succ から m = k.succ + i を復元
        have h1 : m = k.succ + i :=
          Nat.eq_add_of_sub_eq hi h_eq
        -- そこから m - (i+1) を計算
        calc
          m - (i+1)
              = (k.succ + i) - (i+1) := by simp [h1]
          _   = (k + (i+1)) - (i+1) := by
                  have : k.succ + i = k + (i+1) := by
                    -- k.succ + i = (k+1)+i = k+(1+i) = k+(i+1)
                    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
                  simp [this]
          _   = k := by
                  -- (k + (i+1)) - (i+1) = k
                  simp [Nat.add_sub_cancel k (i+1)]

      -- (3) clearPivotCol_loop を1段だけ展開
      unfold clearPivotCol_loop
      simp [hi_lt]

      -- ここでゴールは
      --   (if hrow : i = row then ... else ...) .A.size = m
      -- の形になっているので、さらに行で分岐
      by_cases hrow : i = row
      · -- pivot 行なら R のまま i+1 に進む
        simp [hrow]  -- ゴールが (clearPivotCol_loop R row col hcol (i+1)).A.size = m になる
        have : row + 1 ≤ m := by
          rw [hrow.symm]
          exact hi_succ_le
        have hrow_eq : m - (row + 1) = k := by
          rw [hrow.symm]
          exact hk_eq
        exact IH (i := row+1) (R := R) this hrow_eq
      · -- pivot 以外の行なら rAxpy した R' で i+1 へ
        -- simp で rAxpy が出てくる
        simp [hrow]  -- ゴールが (clearPivotCol_loop (rAxpy R i row _) row col hcol (i+1)).A.size = m
        -- IH は R に関して何も仮定していないので、そのまま使える
        exact IH (i := i+1) (R := _) hi_succ_le hk_eq
    · -- (4) i < m でないならループ終了
      -- hi : i ≤ m と ¬ (i < m) から i = m を得る
      have hmi_le : m ≤ i :=
        Nat.le_of_not_gt (by simpa using hi_lt)
      have h_eq_i : i = m := Nat.le_antisymm hi hmi_le
      -- clearPivotCol_loop R row col hcol m = R
      have hR : (clearPivotCol_loop R row col hcol m) = R := by
        simp [clearPivotCol_loop]
      -- 行数は R の rowSize
      simpa [h_eq_i, hR] using R.rowSize

lemma preserve_rowSize_clearPivotCol_loop
  {m n K} [Field K]
  (row col : Nat) (hcol : col < n) :
  ∀ (i : Nat) (R : Rectified m n K),
    i ≤ m →
    (clearPivotCol_loop R row col hcol i).A.size = m := by
  intro i R hi
  -- k := m - i を measure にとった aux を使う
  have := preserve_rowSize_clearPivotCol_loop_aux (m:=m) (n:=n) (K:=K)
              (row:=row) (col:=col) (hcol:=hcol)
              (k := m - i) (i := i) (R := R) hi rfl
  exact this

lemma preserve_rowSize_clearPivotCol
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hcol : col < n) :
  (clearPivotCol R row col hcol).A.size = m := by
  simpa [clearPivotCol] using
    preserve_rowSize_clearPivotCol_loop row col hcol 0 R

lemma preserve_rect_clearPivotCol_loop_aux
  {m n K} [Field K]
  (row col : Nat) (hcol : col < n) :
  ∀ k,
    ∀ {i : Nat} (R : Rectified m n K),
      i ≤ m →
      m - i = k →
      Rect (clearPivotCol_loop R row col hcol i).A n := by
  intro k
  refine Nat.rec
    (motive := fun k =>
      ∀ {i : Nat} (R : Rectified m n K),
        i ≤ m → m - i = k →
        Rect (clearPivotCol_loop R row col hcol i).A n)
    ?base
    ?step
    k
  · ----------------------------------------------------------------
    -- base: k = 0
    ----------------------------------------------------------------
    intro i R hi h_eq
    -- m - i = 0 かつ i ≤ m なら i = m
    have hmi_le : m ≤ i :=
      Nat.sub_eq_zero_iff_le.mp h_eq
    have h_eq_i : i = m := Nat.le_antisymm hi hmi_le

    have hR : clearPivotCol_loop R row col hcol m = R := by
      simp [clearPivotCol_loop]

    -- Rect は R.rect から
    simp [h_eq_i, hR]
    exact R.rect

  · ----------------------------------------------------------------
    -- step: k → k.succ
    ----------------------------------------------------------------
    intro k IH i R hi h_eq
    classical
    by_cases hi_lt : i < m
    · --------------------------------------------------------------
      -- ケース1: i < m → ループ本体に入る
      --------------------------------------------------------------
      have hi_succ_le : i.succ ≤ m := Nat.succ_le_of_lt hi_lt

      -- m - i = k.succ から m - (i+1) = k を作る
      have hk_eq : m - (i+1) = k := by
        have hi_le : i ≤ m := hi
        -- h_eq : m - i = k.succ ↔ m = k.succ + i
        have h1 : m = k.succ + i :=
          Nat.eq_add_of_sub_eq hi h_eq
        calc
          m - (i+1)
              = (k.succ + i) - (i+1) := by simp [h1]
          _   = (k + (i+1)) - (i+1) := by
                  have : k.succ + i = k + (i+1) := by
                    simp [Nat.succ_eq_add_one, Nat.add_left_comm, Nat.add_comm]
                  simp [this]
          _   = k := by
                  simp

      -- 1ステップだけ unfold して、行 = row / ≠ row でさらに分岐
      unfold clearPivotCol_loop
      simp [hi_lt]  -- if hi : i < m を潰す

      by_cases hrow : i = row
      · ------------------------------------------------------------
        -- (a) pivot 行なら R のまま i+1 に進むケース
        ------------------------------------------------------------
        simp [hrow]  -- clearPivotCol_loop R ... (i+1)
        have : row + 1 ≤ m := by
          rw [hrow.symm]
          exact hi_succ_le
        have hk_eq : m - (row + 1) = k := by
          rw [hrow.symm]
          exact hk_eq
        exact IH (i := row+1) (R := R) this hk_eq

      · ------------------------------------------------------------
        -- (b) pivot 以外の行なら rAxpy して i+1 に進むケース
        ------------------------------------------------------------
        -- simp すると R' := rAxpy R i row (-a) が出てくる
        -- ここで R' は Rectified m n K なので rect は R'.rect
        simp [hrow]  -- goal: Rect (clearPivotCol_loop (rAxpy R i row _) _ _ _ (i+1)).A n
        -- そのまま IH に渡せる
        exact IH (i := i+1) (R := _) hi_succ_le hk_eq

    · --------------------------------------------------------------
      -- ケース2: ¬ i < m → m - i = 0 になるので k.succ と矛盾（到達不能ケース）
      --------------------------------------------------------------
      have hi_ge : m ≤ i := Nat.le_of_not_lt hi_lt
      have hzero : m - i = 0 := Nat.sub_eq_zero_of_le hi_ge
      -- h_eq : m - i = k.succ
      -- hzero : m - i = 0
      -- → 0 = k.succ
      have hk0 : k.succ = 0 := by
        have : 0 = k.succ := by
          rw [←h_eq, ←hzero]
        -- h_eq : m - i = k.succ, hzero : m - i = 0
        -- なので k.succ = 0
        simp [this]
      exact (Nat.succ_ne_zero _ hk0).elim

lemma preserve_rect_clearPivotCol_loop
  {m n K} [Field K]
  (row col : Nat) (hcol : col < n) :
  ∀ (i : Nat) (R : Rectified m n K),
    i ≤ m →
    Rect (clearPivotCol_loop R row col hcol i).A n := by
  intro i R hi
  -- k := m - i で aux をそのまま使う
  have := preserve_rect_clearPivotCol_loop_aux
              (m := m) (n := n) (K := K)
              (row := row) (col := col) (hcol := hcol)
              (k := m - i) (i := i) (R := R) hi rfl
  exact this

lemma preserve_rect_clearPivotCol
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hcol : col < n) :
  Rect (clearPivotCol R row col hcol).A n := by
  -- clearPivotCol は 0 からループを開始するだけ
  unfold clearPivotCol
  have := preserve_rect_clearPivotCol_loop
              (m := m) (n := n) (K := K)
              (row := row) (col := col) (hcol := hcol)
              0 R (Nat.zero_le _)
  simpa using this


-- echelon form の保存証明
-- pivot関数の拡張
def extendPivot {r n : Nat} (p : Fin r → Fin n) (c : Fin n) :
  Fin (r+1) → Fin n :=
  fun i' => if h : i'.val < r then p ⟨i'.val, h⟩ else c

lemma extendPivot_strictMono
  {r n} {p : Fin r → Fin n} (hp : StrictMono p)
  {c : Fin n} (hc : ∀ i, p i < c) :
  StrictMono (extendPivot p c) := by
  intro i j hij
  have hij' : (i : Nat) < (j : Nat) := (Fin.lt_iff_val_lt_val).1 hij
  by_cases hi : (i : Nat) < r
  · -- i は「内部」側
    by_cases hj : (j : Nat) < r
    · -- 両方「内部」: hp を使うだけ
      have hpp : p ⟨i, hi⟩ < p ⟨j, hj⟩ := hp hij
      simpa [extendPivot, hi, hj] using hpp
    · -- i は内部, j は境界 (= r)
      have hj_le : (j : Nat) ≤ r :=
        Nat.le_of_lt_succ (by simp [Nat.succ_eq_add_one, j.is_lt])
      have hj_ge : r ≤ (j : Nat) := le_of_not_gt (by simpa using hj)
      have hj_eq : (j : Nat) = r := le_antisymm hj_le hj_ge
      have hpc : p ⟨i, hi⟩ < c := hc ⟨i, hi⟩
      simpa [extendPivot, hi, hj] using hpc
  · -- i は境界 (= r)
    have hi_le : (i : Nat) ≤ r :=
      Nat.le_of_lt_succ (by simp [Nat.succ_eq_add_one, i.is_lt])
    have hi_ge : r ≤ (i : Nat) := le_of_not_gt (by simpa using hi)
    have hi_eq : (i : Nat) = r := le_antisymm hi_le hi_ge
    by_cases hj : (j : Nat) < r
    · -- これは矛盾: i = r < j ≤ r は成り立たない
      have hj_le : (j : Nat) ≤ r :=
        Nat.le_of_lt_succ (by simp [Nat.succ_eq_add_one, j.is_lt])
      have : r < r := Nat.lt_of_lt_of_le (by simpa [hi_eq] using hij') hj_le
      exact (lt_irrefl _ this).elim
    · -- どちらも境界 (= r) は i < j と両立しないので矛盾で潰す
      have hj_le : (j : Nat) ≤ r :=
        Nat.le_of_lt_succ (by simp [Nat.succ_eq_add_one, j.is_lt])
      have hj_ge : r ≤ (j : Nat) := le_of_not_gt (by simpa using hj)
      have hj_eq : (j : Nat) = r := le_antisymm hj_le hj_ge
      -- ここで (i:ℕ)=r=(j:ℕ) だが hij' : (i:ℕ) < (j:ℕ) なので矛盾
      have : (i : Nat) < (i : Nat) := by simp [hi_eq, hj_eq] at hij'
      exact (lt_irrefl _ this).elim

/- echelon form の途中形 -/
/- ループ不変量 : 状態 R（配列＋Rect 証明）、列ポインタ c、確定ピボット行数 r、
ピボット写像 p : Fin r → Fin n（「i 行のピボットは列 p i」）を持って、次を仮定として保つ -/
structure Inv
  {m n} {α : Type u} [Field α] (M0 : Matrix (Fin m) (Fin n) α)
  (R0 : Rectified m n α) (r0 c0 : Nat) (p0 : Fin r0 → Fin n) : Prop where
  (I0_rows : R0.A.size = m)   -- 構造
  (I0_rect : Rect R0.A n)     -- 構造
  (I1_bound : r0 ≤ m ∧ c0 ≤ n) -- 境界
  (I1_mono  : StrictMono p0)  -- ピボット列は増加
  (I1_in    : ∀ i, p0 i < c0)   -- ピボット列は c 未満
  (I2_unit  :                     -- ピボット列は縦に単位ベクトル
    ∀ i : Fin r0, (matOf R0) (Fin.castLE I1_bound.1 i) (p0 i) = 1 ∧
      ∀ i' : Fin m, i' ≠ Fin.castLE I1_bound.1 i  → (matOf R0) i' (p0 i) = 0)
  (I3_left0 :
    ∀ i : Fin r0, ∀ j : Fin n,
      (j : Nat) < (p0 i : Nat) → (matOf R0) (Fin.castLE I1_bound.1 i) j = 0)
  (I4_tail0 :
    ∀ j : Fin n, (j : Nat) < c0 →
      (∀ i : Fin r0, p0 i ≠ j) →
      ∀ i' : Fin m, (r0 : Nat) ≤ (i' : Nat) → (matOf R0) i' j = 0)
  (I5_fac :
    ∃ (E : Matrix (Fin m) (Fin m) α), IsUnit E ∧ matOf R0 = E * M0)

lemma inv_init
  {K : Type u} [Field K] {m n : ℕ}
  (M0 : Matrix (Fin m) (Fin n) K)
  (R0 : Rectified m n K)
  (h0 : matOf R0 = M0) :
  Inv M0 R0 0 0 (Fin.elim0) := by
  classical
  refine
  { I0_rows := R0.rowSize
  , I0_rect := R0.rect
  , I1_bound := ⟨Nat.zero_le _, Nat.zero_le _⟩
  , I1_mono := by intro i j hij; exact i.elim0  -- Fin 0 は空
  , I1_in   := by intro i; exact i.elim0        -- 同上：p i < 0 は空
  , I2_unit := by intro i; exact i.elim0        -- 同上
  , I3_left0 := by intro i; exact i.elim0       -- 同上
  , I4_tail0 := by
      -- j : Fin n, (j:ℕ) < 0 は偽なので ex falso
      intro j hj _ i' hi'
      exact False.elim ((Nat.not_lt.mpr (Nat.zero_le _)) hj)
  , I5_fac := by
      refine ⟨(1 : Matrix (Fin m) (Fin m) K), isUnit_one, ?_⟩
      -- matOf R0 = 1 * M0 を示す。右を one_mul で簡約。
      simpa [one_mul] using h0
  }

/- 実行用の状態（証明なし） -/
structure GEExecState (m n : Nat) (K : Type u) where
  M0 : Matrix (Fin m) (Fin n) K
  R : Rectified m n K
  rowCount : Nat
  colPtr   : Nat
  piv : Fin rowCount → Fin n

/- 任意の体 K に対する「証明持ち」ガウス消去状態 -/
structure GEStateP (m n : Nat) (K : Type u) [Field K] where
  M0 : Matrix (Fin m) (Fin n) K
  R : Rectified m n K
  rowCount : Nat
  colPtr   : Nat
  pivot    : Fin rowCount → Fin n
  inv      : Inv
              (M0 := M0)
              (R0 := R)
              (r0 := rowCount)
              (c0 := colPtr)
              (p0 := pivot)

/- 証明の消去関数 -/
def erase {m n K} [Field K] (st : GEStateP m n K) : GEExecState m n K :=
  { M0 := st.M0, R := st.R, rowCount := st.rowCount, colPtr := st.colPtr, piv := st.pivot }

-- 停止条件（K に依存しない）
def doneP {m n} {K : Type u} [Field K] (st : GEStateP m n K) : Prop :=
  ¬ (st.rowCount < m ∧ st.colPtr < n)

def doneExecP {m n} {K : Type u} [Field K] (st : GEExecState m n K) : Prop :=
  ¬ (st.rowCount < m ∧ st.colPtr < n)

lemma doneP_iff_rEqm_or_cEqn {m n} {K : Type u} [Field K] (st : GEStateP m n K) :
  doneP st ↔ st.rowCount = m ∨ st.colPtr = n := by
  simp [doneP]
  constructor
  · -- → 方向
    intro hdone
    by_contra hcontra
    push_neg at hcontra
    have st.rowCount_le_m : st.rowCount ≤ m := by
      exact st.inv.I1_bound.1
    have st.rowCount_lt_m : st.rowCount < m := Nat.lt_of_le_of_ne st.rowCount_le_m hcontra.left
    have st.colPtr_le_n : st.colPtr ≤ n := by
      exact st.inv.I1_bound.2
    have st.colPtr_lt_n : st.colPtr < n := Nat.lt_of_le_of_ne st.colPtr_le_n hcontra.right
    have st.colPtr_n_le_neg : ¬ (n ≤ st.colPtr) := by
      simp [st.colPtr_lt_n]
    have : n ≤ st.colPtr := hdone st.rowCount_lt_m
    exact st.colPtr_n_le_neg this
  · -- ← 方向
    intro hdisj hcond
    have hrow_ne : st.rowCount ≠ m := by
      intro h_eq
      -- hcond : st.rowCount < m を m < m に書き換え
      have hm_lt : m < m := by
        simp [h_eq] at hcond
      exact (lt_irrefl m hm_lt)

    have hcol_eq : st.colPtr = n := Or.resolve_left hdisj hrow_ne

    exact Nat.le_of_eq hcol_eq.symm

-- ==============================
-- pivot探索（汎用版）
-- ==============================

/- find pivot の理論版 -/
/- 行番号 r が pivot 候補であることを表す述語 -/
-- i = r という Nat と Fin m の変換が入っている点に注意
def PivotIndexPred
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n)
  (r : Nat) : Prop :=
  ∃ (i : Fin m),
    (i : Nat) = r ∧
    (st.rowCount : Nat) ≤ r ∧
    (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0


noncomputable def findPivot_spec
  {m n K} [Field K] (st : GEStateP m n K) (hcol : st.colPtr < n) :
  Option (Fin m) :=
by
  classical
  -- 「どこかに pivot 行番号が存在するか？」という命題
  let Hex : Prop := ∃ r : Nat, PivotIndexPred st hcol r
  by_cases h : Hex
  · -- pivot が存在する場合：最小の r = Nat.find h を取る
    have hP : PivotIndexPred st hcol (Nat.find h) := Nat.find_spec h
    exact some (Classical.choose hP)
  · -- pivot が存在しない場合：none
    exact none

/- rowCount 行目以降で、列 colPtr が非零の行があるか? -/
def HasPivotPred
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n) : Prop :=
  ∃ i : Fin m,
    (st.rowCount : Nat) ≤ i ∧
    (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0

def IsFirstPivotIndex
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n)
  (i0 : Fin m) : Prop :=
  (st.rowCount : Nat) ≤ i0 ∧
  (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 ∧
  ∀ r : Fin m,
    st.rowCount ≤ r →
    r < i0 →
    (matOf st.R) r ⟨st.colPtr, hcol⟩ = 0


lemma existsPivotIndex_iff_existsNonzero
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n) :
  (∃ r : Nat, PivotIndexPred st hcol r) ↔
    ∃ i : Fin m,
      (st.rowCount : Nat) ≤ i ∧
      (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0 := by
  constructor
  · -- → 方向
    rintro ⟨r, hP⟩
    rcases hP with ⟨i, hi_r, hi_ge, hi_nz⟩
    -- r = i.val を使って i を証人にすれば OK
    subst hi_r
    exact ⟨i, hi_ge, hi_nz⟩
  · -- ← 方向
    rintro ⟨i, hi_ge, hi_nz⟩
    refine ⟨(i : Nat), ?_⟩
    refine ⟨i, ?_, hi_ge, hi_nz⟩
    rfl


lemma findPivot_spec_eq_none_iff
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n) :
  findPivot_spec st hcol = none
    ↔ ¬ HasPivotPred st hcol :=
by
  classical
  -- 省略記法
  let Hex : Prop := ∃ r : Nat, PivotIndexPred st hcol r
  have hexEquiv :
    Hex ↔ ∃ i : Fin m,
      (st.rowCount : Nat) ≤ i ∧
      (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0 :=
    existsPivotIndex_iff_existsNonzero (st:=st) (hcol:=hcol)

  constructor
  · -- ( = none ) → (非存在)
    intro hEq hexSimple
    -- hexSimple から Hex を作る
    have hHex : Hex := (hexEquiv.mpr hexSimple)
    -- def を展開して if_pos hHex に簡約
    unfold findPivot_spec at hEq
    -- if_pos になるので left-hand side は some _ になってしまう → 矛盾
    simp [Hex, hHex] at hEq
  · -- (非存在) → ( = none )
    intro hNoSimple
    -- まず Hex が偽であることを言う
    have hNoHex : ¬ Hex := by
      intro hHex
      -- Hex から「単純な存在」を引き出して hNoSimple と矛盾させる
      have hexSimple :
        ∃ i : Fin m,
          (st.rowCount : Nat) ≤ i ∧
          (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0 :=
        hexEquiv.mp hHex
      exact hNoSimple hexSimple

    -- Hex が偽なら if_neg で none に簡約される
    unfold findPivot_spec
    simp [Hex, hNoHex]


/- pivotが見つからなかった場合、その列はr以降すべて0 -/
lemma findPivot_spec_none_sound
  {m n K} [Field K]
  {st : GEStateP m n K}
  (hcol : st.colPtr < n)
  (h : findPivot_spec st hcol = none) :
  ∀ i : Fin m, (st.rowCount : Nat) ≤ i →
    (matOf st.R) i ⟨st.colPtr, hcol⟩ = 0 := by

    have hnone :
    ¬ ∃ i : Fin m,
      (st.rowCount : Nat) ≤ i ∧
      (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0 :=
        (findPivot_spec_eq_none_iff st hcol).1 h

    intro i hi
    -- もし 0 でないと仮定すると矛盾
    by_contra hne
    -- そうすると「rowCount 以降で非零なものがある」という存在を作れてしまう
    exact hnone ⟨i, hi, hne⟩

/- pivot が見つかった場合、その i0 行が確かに非零 -/
/- pivot が見つかった場合、その i0 行が確かに非零 -/
lemma findPivot_spec_some_sound
  {m n K} [Field K]
  {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (h : findPivot_spec st hcol = some i0) :
  (st.rowCount : Nat) ≤ i0 ∧
  (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 := by
  classical

  -- findPivot_spec の定義で使っている命題
  let Hex : Prop := ∃ r : Nat, PivotIndexPred st hcol r

  -- Hex が偽だと findPivot_spec = none となり、h : some i0 と矛盾 → Hex は真
  have hHex : Hex := by
    by_contra hFalse
    -- findPivot_spec st hcol = none と分かる
    have hnone : findPivot_spec st hcol = none := by
      unfold findPivot_spec
      simp [Hex, hFalse]
    -- しかし h : findPivot_spec st hcol = some i0 と矛盾
    have : some i0 = none := by simp [h] at hnone
    exact Option.noConfusion this

  -- Nat.find で「一番小さい」pivot 行番号を取る
  have hP : PivotIndexPred st hcol (Nat.find hHex) :=
    Nat.find_spec hHex

  -- h から、実際に返しているのが Classical.choose hP であることを引き出す
  have h' := h
  unfold findPivot_spec at h'
  -- 定義の中で Nat.find_spec hHex = hP と見なせる
  have h'' :
    some (Classical.choose hP) = some i0 := by
    simpa [Hex, hHex, hP] using h'

  -- some の injectivity
  have hi0 :
    Classical.choose hP = i0 :=
    Option.some.inj h''

  -- PivotIndexPred から Classical.choose hP に関する性質を取り出す
  rcases Classical.choose_spec hP with
    ⟨h_val_eq, h_ge, h_nz⟩
  -- h_ge : rowCount ≤ Nat.find hHex を
  -- rowCount ≤ ↑(Classical.choose hP) に書き換える

  -- まず ∃ の形をした補題として取り直す
  have hP_ex :
    ∃ i : Fin m,
      (i : Nat) = Nat.find hHex ∧
      (st.rowCount : Nat) ≤ Nat.find hHex ∧
      (matOf st.R) i ⟨st.colPtr, hcol⟩ ≠ 0 :=
    hP  -- ← PivotIndexPred の定義そのもの

  -- choose_spec を使って性質を取り出す
  have h_spec :
    ((Classical.choose hP : Fin m) : Nat) = Nat.find hHex ∧
    (st.rowCount : Nat) ≤ Nat.find hHex ∧
    (matOf st.R) (Classical.choose hP) ⟨st.colPtr, hcol⟩ ≠ 0 :=
    Classical.choose_spec hP_ex

  rcases h_spec with ⟨h_eq, h_ge, h_nz⟩

  -- rowCount ≤ (Classical.choose hP).val へ書き換え
  have h_ge_choose :
    (st.rowCount : Nat) ≤ ((Classical.choose hP : Fin m) : Nat) := by
    rw [h_eq]
    exact h_ge

  -- (i0 : Nat) = Nat.find hHex を得る
  have hi0_nat_eq :
    (i0 : Nat) = Nat.find hHex := by
    -- hi_eq : Classical.choose hP = i0 を nat 値に持ち上げてから h_val_eq と合成
    have : ((i0 : Fin m) : Nat) =
          ((Classical.choose hP : Fin m) : Nat) := by
      rw [hi0]
    -- これと h_val_eq を合わせればよい
    calc
      (i0 : Nat)
          = ((Classical.choose hP : Fin m) : Nat) := this
      _   = Nat.find hHex := h_val_eq

  have h_ge' :
    (st.rowCount : Nat) ≤ (i0 : Nat) := by
    rw [hi0_nat_eq]
    exact h_ge

  have hP_spec :
    (st.rowCount : Nat) ≤ (i0 : Nat) ∧
    (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 := by
    rw [hi0] at h_nz
    exact ⟨h_ge', h_nz⟩

  -- これを i0 についての主張に書き換え
  have hP_spec_i0 :
    (st.rowCount : Nat) ≤ i0 ∧
    (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 := by
    simpa [hi0] using hP_spec

  exact hP_spec_i0


lemma findPivot_spec_some_min
  {m n K} [Field K]
  {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (h : findPivot_spec st hcol = some i0) :
  PivotIndexPred st hcol i0.val ∧
  ∀ r : Nat,
    st.rowCount ≤ r →
    r < i0.val →
    ¬ PivotIndexPred st hcol r := by
  classical
  -- spec の内部で使っている述語
  let Hex : Prop := ∃ r : Nat, PivotIndexPred st hcol r

  -- まず Hex が真であることを示す
  have hHex : Hex := by
    by_contra hFalse
    -- Hex が偽なら findPivot_spec は none になる
    have hnone : findPivot_spec st hcol = none := by
      unfold findPivot_spec
      simp [Hex, hFalse]
    -- でも今は some i0 だと仮定しているので矛盾
    have : some i0 = none := by simp [h] at hnone
    exact Option.noConfusion this

  -- 以降 Nat.find hHex を使うので、外に出しておく
  -- （なくてもいいけど読みやすさのため）
  have hP : PivotIndexPred st hcol (Nat.find hHex) :=
    Nat.find_spec hHex

  -- h から、実際に返しているのが Classical.choose hP であることを引き出す
  have h' := h
  unfold findPivot_spec at h'
  -- if_pos hHex で右辺が some (Classical.choose hP) に簡約される
  have h'' :
    some (Classical.choose hP) = some i0 := by
    simpa [Hex, hHex, hP] using h'

  -- some の injectivity から中身の Fin m が等しい
  have hi0 :
    Classical.choose hP = i0 :=
    Option.some.inj h''

  -- PivotIndexPred st hcol (Nat.find hHex) を「∃i : Fin m, …」の形で取り出す
  -- ここで hP : PivotIndexPred st hcol (Nat.find hHex)
  --     = ∃ i : Fin m, (i : Nat) = Nat.find hHex ∧ … なので、
  -- Classical.choose hP と Classical.choose_spec hP が使える
  rcases Classical.choose_spec hP with
    ⟨h_val_eq, h_ge, h_nz⟩
  -- h_val_eq : ((Classical.choose hP : Fin m) : Nat) = Nat.find hHex

  -- hi0 : Classical.choose hP = i0 から、Nat 値の等しさを得る
  have h_val_eq' :
    (i0 : Nat) = Nat.find hHex := by
    -- まず Fin の等式を Nat に写像
    have : ((Classical.choose hP : Fin m) : Nat) = (i0 : Nat) := by
      rw [hi0]
    -- これと h_val_eq を合成
    calc
      (i0 : Nat)
          = ((Classical.choose hP : Fin m) : Nat) := this.symm
      _   = Nat.find hHex := h_val_eq

  -- 求める形にまとめる（向きに注意：i0.val = Nat.find hHex）
  constructor
  · -- 最小性のうち、PivotIndexPred st hcol i0.val
    simp [h_val_eq', hP]
  · -- 最小性のうち、∀ r < i0.val, ¬
    intro r hr_ge hr_lt hP_r

    have hr_lt' : r < Nat.find hHex := by
      rw [h_val_eq'] at hr_lt
      exact hr_lt

    have h_le : Nat.find hHex ≤ r := Nat.find_min' hHex hP_r

    have : Nat.find hHex < Nat.find hHex := Nat.lt_of_le_of_lt h_le hr_lt'

    exact (lt_irrefl _ this).elim

lemma findPivot_spec_eq_some_iff
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n) (i0 : Fin m) :
  findPivot_spec st hcol = some i0
    ↔ IsFirstPivotIndex st hcol i0 := by
  classical
  constructor
  · intro h
    -- 「非ゼロ & rowCount 以上」は `findPivot_spec_some_sound` から
    have h_sound :=
      findPivot_spec_some_sound (st := st) (i0 := i0) hcol h
    -- 「i0 より前は全部ゼロ」は `findPivot_spec_some_min` から
    have h_min :=
      findPivot_spec_some_min (st := st) (i0 := i0) hcol h
    rcases h_sound with ⟨h_ge, h_nz⟩
    refine ⟨h_ge, h_nz, ?_⟩
    intro r hr_ge hr_lt
    -- ここで h_min から「r では PivotIndexPred が成り立たない」ことを取り出し、
    -- ≠0 だと仮定すると PivotIndexPred r を構成できるので矛盾させる
    have h_not :
      ¬ PivotIndexPred st hcol r := (h_min.2 r hr_ge hr_lt)
    by_contra h_ne
    -- h_ne : (matOf st.R) ⟨r, ?⟩ col ≠ 0 から PivotIndexPred st hcol r を作る
    have : PivotIndexPred st hcol r := by
      refine ⟨⟨r, ?_⟩, ?_, hr_ge, h_ne⟩
      · -- r < m の証明
        -- st.R.rowSize : st.R.A.size = m を使って（細かいだけ）
        have hi0m : (i0 : Nat) < m := i0.is_lt
        exact Nat.lt_trans hr_lt hi0m
      · rfl
    exact h_not this
  · intro hFirst
    -- 逆向きは、「IsFirstPivotIndex を満たす i0 が一意である」
    -- ということから、Nat.find hHex = i0 だと分かり、
    -- その `Nat.find` を使ってる `findPivot_spec` の定義と合うことを示す
    -- （`findPivot_spec_some_min` の証明でやっているのとほぼ同じノリ）
    classical
    rcases hFirst with ⟨h0_ge, h0_nz, h0_zero_before⟩
    have h_has : HasPivotPred st hcol := ⟨i0, h0_ge, h0_nz⟩

    cases hspec : findPivot_spec st hcol with
    | none =>
        -- none なら h_has と矛盾
        have hnone_iff := findPivot_spec_eq_none_iff st hcol
        have h_no_pivot : ¬ HasPivotPred st hcol := hnone_iff.1 hspec
        exact False.elim (h_no_pivot h_has)
    | some j =>
        have h_sound :=
          findPivot_spec_some_sound (st := st) (i0 := j) hcol hspec
        have h_min :=
          findPivot_spec_some_min (st := st) (i0 := j) hcol hspec
        rcases h_sound with ⟨hj_ge, hj_nz⟩
        rcases h_min with ⟨hjPiv, h_min'⟩
        -- i0.val ≤ j.val を示す
        have h_le1 : (i0 : Nat) ≤ (j : Nat) := by
          by_contra hlt
          have hj_lt : (j : Nat) < (i0 : Nat) := lt_of_not_ge hlt
          -- h0_zero_before を r = j.val に適用
          have hzero :
            (matOf st.R) ⟨(j : Nat), by exact j.is_lt⟩
              ⟨st.colPtr, hcol⟩ = 0 :=
            h0_zero_before j hj_ge hj_lt
          -- Fin ext で j に書き換え
          have hzero' :
            (matOf st.R) j ⟨st.colPtr, hcol⟩ = 0 := by
            have : (⟨(j : Nat), j.is_lt⟩ : Fin m) = j := by
              ext; rfl
            simpa [this] using hzero
          exact hj_nz hzero'
        -- j.val ≤ i0.val を示す
        have h_le2 : (j : Nat) ≤ (i0 : Nat) := by
          by_contra hlt
          have hi_lt : (i0 : Nat) < (j : Nat) := lt_of_not_ge hlt
          -- i0 も pivot なので PivotIndexPred st hcol i0.val が立つ
          have hPiv0 : PivotIndexPred st hcol (i0 : Nat) := by
            refine ⟨i0, rfl, h0_ge, h0_nz⟩
          -- しかし h_min' によると r < j.val では pivot 不可
          have h_not : ¬ PivotIndexPred st hcol (i0 : Nat) :=
            h_min' (i0 : Nat) h0_ge hi_lt
          exact h_not hPiv0
                -- 2 つの不等式から val の等式
        have h_eqNat : (j : Nat) = (i0 : Nat) :=
          le_antisymm h_le2 h_le1

        -- Fin ext で j = i0
        have hj_eq : j = i0 := by
          apply Fin.ext
          exact h_eqNat

        -- 最後にゴールを得る
        simp [hj_eq]

-- i が pivot 行番号であり、かつそのような行番号が一意であることを示す
lemma IsFirstPivotIndex_unique
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n)
  {i1 i2 : Fin m}
  (h1 : IsFirstPivotIndex st hcol i1)
  (h2 : IsFirstPivotIndex st hcol i2) :
  i1 = i2 := by
  rcases h1 with ⟨h1_ge, h1_nz, h1_zero_before⟩
  rcases h2 with ⟨h2_ge, h2_nz, h2_zero_before⟩
  -- まず値で比較
  have : (i1 : Nat) = (i2 : Nat) := by
    -- 片方を仮に小さいと仮定して矛盾を出す
    by_contra hne
    have hlt_or : (i1 : Nat) < (i2 : Nat) ∨ (i2 : Nat) < (i1 : Nat) :=
      lt_or_gt_of_ne hne
    cases hlt_or with
    | inl hlt =>
        -- i1 < i2 なら、h2_zero_before を r = i1.val に適用できる
        have hzero :
          (matOf st.R) ⟨(i1 : Nat), by exact i1.is_lt⟩ ⟨st.colPtr, hcol⟩ = 0 :=
          h2_zero_before i1 h1_ge hlt
        -- Fin ext で i1 に書き換え
        have hzero' :
          (matOf st.R) i1 ⟨st.colPtr, hcol⟩ = 0 := by
          have : (⟨(i1 : Nat), i1.is_lt⟩ : Fin m) = i1 := by ext; rfl
          simpa [this] using hzero
        exact h1_nz hzero'
    | inr hlt =>
        -- 対称に i2 < i1 なら h1_zero_before に r = i2.val を入れて矛盾
        have hzero :
          (matOf st.R) ⟨(i2 : Nat), by exact i2.is_lt⟩ ⟨st.colPtr, hcol⟩ = 0 :=
          h1_zero_before i2 h2_ge hlt
        have hzero' :
          (matOf st.R) i2 ⟨st.colPtr, hcol⟩ = 0 := by
          have : (⟨(i2 : Nat), i2.is_lt⟩ : Fin m) = i2 := by ext; rfl
          simpa [this] using hzero
        exact h2_nz hzero'

  -- Fin の ext
  apply Fin.ext
  exact this


/- find pivot の実行版 -/

-- コアな再帰部分だけを外出し
def findPivot_loop {m n K} [Field K] [DecidableEq K]
  (R : Rectified m n K) (rowCount colPtr : Nat)
  (hcol : colPtr < n) :
  Nat → Option (Fin m)
| i =>
  let mSz := R.A.size
  let c   := colPtr
  if hi : i < mSz then
    if hrow : rowCount ≤ i then
      let row := R.A[i]
      have hiA : i < R.A.size := by
        simpa [mSz] using hi
      have hrowlen : row.size = n := by
        have := R.rect i hiA
        simpa [row] using this
      have hj : c < row.size := by
        have hc : c < n := hcol
        simpa [hrowlen] using hc
      let a : K := row[c]
      if hne : a ≠ 0 then
        have hi_m : i < m := by
          have := R.rowSize
          have hm : mSz = m := by simpa [mSz] using this
          simpa [hm] using hi
        some ⟨i, hi_m⟩
      else
        findPivot_loop R rowCount colPtr hcol (i+1)
    else
      findPivot_loop R rowCount colPtr hcol (i+1)
  else
    none
termination_by  i => R.A.size - i
-- decreasing_by

-- exec は「rowCount からスタートする loop」
def findPivot_exec {m n K} [Field K] [DecidableEq K]
  (st : GEExecState m n K) (hcol : st.colPtr < n) : Option (Fin m) :=
  findPivot_loop st.R st.rowCount st.colPtr hcol st.rowCount


lemma matOf_entry_eq_get
  {m n K} [Field K]
  (R : Rectified m n K)
  {c : Nat} (hc : c < n)
  {i : Nat} (hi : i < m) :
  (matOf R) ⟨i, hi⟩ ⟨c, hc⟩
    =
  (R.A[i]'(by
    -- まず i < R.A.size を作る
    -- R.rowSize : R.A.size = m
    have : i < m := hi
    have : i < R.A.size := by simpa [R.rowSize] using this
    exact this
  ))[c]'(by
    -- 次に c < (R.A[i]).size を作る
    -- 1. i < R.A.size
    have hiA : i < R.A.size := by
      simpa [R.rowSize] using hi
    -- 2. 行 i の長さが n
    have hrowlen : (R.A[i]'hiA).size = n := by
      -- R.rect : Rect R.A n = ∀ i hi, (A[i]).size = n
      have := R.rect i hiA
      simpa using this
    -- 3. st.colPtr < n から c < row.size
    have : c < (R.A[i]'hiA).size := by
      simpa [hrowlen] using hc
    exact this)
  := by
  -- 左辺：matOf → toMat → Array の get に展開して simp
  simp [matOf, toMat]

lemma findPivot_loop_some_of_hasPivot
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K) (hcol : stP.colPtr < n)
  (h_has : HasPivotPred stP hcol) :
  ∃ i0 : Fin m,
    findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount = some i0 := by
  classical
  rcases h_has with ⟨i, hi_ge, hi_nz⟩

  let mSz := stP.R.A.size
  have hAsize : stP.R.A.size = m := stP.R.rowSize
  have hi_m : (i : Nat) < m := i.is_lt
  have hiA : (i : Nat) < mSz := by
    simp [mSz, hAsize, hi_m]

  let c := stP.colPtr
  have hc : c < n := hcol

  -- d := i - k で再帰
  have aux :
    ∀ d k,
      (i : Nat) - k = d →
      stP.rowCount ≤ k →
      k ≤ (i : Nat) →
      ∃ i0 : Fin m,
        findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0 := by
    intro d
    induction d with
    | zero =>
        -- ===== base: d = 0 =====
        intro k hk_d hk_row hk_le
        -- i - k = 0 から i ≤ k
        have hi_le_k : (i : Nat) ≤ k := Nat.le_of_sub_eq_zero hk_d
        -- k ≤ i と i ≤ k から k = i
        have hk_eq : k = (i : Nat) := Nat.le_antisymm hk_le hi_le_k
        subst hk_eq   -- 以降 k = i

        -- i 行目が配列範囲内
        have hiA' : (i : Nat) < mSz := hiA
        have hi_m' : (i : Nat) < m := hi_m

        -- matOf の成分と Array アクセスを同一視する補題を使う
        have h_get :
          (matOf stP.R) i ⟨c, hc⟩ =
            (stP.R.A[(i : Nat)]'(
              by
                -- i < A.size
                rw [hAsize]
                exact hi_m'
            ))[c]'(
              by
                -- c < 行サイズ
                have hiA'' : (i : Nat) < stP.R.A.size := by
                  rw [hAsize]
                  exact hi_m'
                have hrowlen :
                  (stP.R.A[(i : Nat)]'hiA'').size = n := by
                  have := stP.R.rect (i : Nat) hiA''
                  simpa using this
                simpa [hrowlen] using hc
            ) := by
          -- これは既にある補題 matOf_entry_eq_get で出せる
          simpa using
            (matOf_entry_eq_get (R := stP.R)
              (c := c) hc
              (i := (i : Nat)) hi_m')

        -- hi_nz : (matOf stP.R) i ⟨c, hc⟩ ≠ 0 から
        -- 実際に loop で見る a も ≠ 0
        have hne_a :
          (stP.R.A[(i : Nat)]'(
            by rw [hAsize]; exact hi_m'
          ))[c]'(
            by
              -- 上と同じ証明。面倒なら `have` でまとめても良い。
              have hiA'' : (i : Nat) < stP.R.A.size := by
                rw [hAsize]; exact hi_m'
              have hrowlen :
                (stP.R.A[(i : Nat)]'hiA'').size = n := by
                have := stP.R.rect (i : Nat) hiA''
                simpa using this
              simpa [hrowlen] using hc
          ) ≠ 0 := by
          have := hi_nz
          -- h_get で書き換える
          simpa [h_get] using this

        -- findPivot_loop の内部での a と一致する形に書き直した "a ≠ 0"
        have hne' :
          (let a : K := stP.R.A[i.val][c]'(
              by
              -- i < A.size
              -- 上と同じ証明。面倒なら `have` でまとめても良い。
              have hiA'' : (i : Nat) < stP.R.A.size := by
                rw [hAsize]; exact hi_m'
              have hrowlen :
                (stP.R.A[(i : Nat)]'hiA'').size = n := by
                have := stP.R.rect (i : Nat) hiA''
                simpa using this
              simpa [hrowlen] using hc
          );
          a) ≠ 0 := by
          simpa using hne_a
        -- hi_row : rowCount ≤ i は hi_ge
        have hi_row : stP.rowCount ≤ (i : Nat) := hi_ge
        -- これで、findPivot_loop の1ステップ目を展開すれば some になる
        refine ⟨i, ?_⟩
        unfold findPivot_loop
        simp [mSz, hiA', hi_row]
        -- simp で if の分岐を全部潰すとちょうど `some ⟨i, hi_m'⟩`
        intro h
        have : False := by
          apply hne'
          simpa [c] using h
        exact this.elim

    | succ d IH =>
        -- step case はここから…
        intro k hk_d hk_row hk_le
        -- （ここはまだ書いてないので、あとで埋める）
        -- まず k < i, k < mSz を取る
        have hk_ne_i : k ≠ (i : Nat) := by
          -- もし k = i なら (i - k) = 0 のはずだが succ d ≠ 0 で矛盾
          intro hk_eq
          subst hk_eq
          simp at hk_d      -- i - i = 0 なので hk_d: 0 = succ d になって矛盾
        have hk_lt_i : k < (i : Nat) := lt_of_le_of_ne hk_le hk_ne_i
        have hk_lt_mSz : k < mSz := by
          -- k ≤ i < mSz から k < mSz
          exact lt_trans hk_lt_i hiA

        -- ここから findPivot_loop の定義を展開
        unfold findPivot_loop
        -- mSz, hk_lt_mSz, hk_row を使って if を 2 段潰す
        -- （rowCount ≤ k なので "hrow" 側に入る）
        simp [mSz, hk_lt_mSz, hk_row]  -- ゴールに「if hne : a ≠ 0 then ... else ...」が出てくるはず
        -- a が 0 かどうかで分岐
        by_cases hz : stP.R.A[k][stP.colPtr]'(
          by
          have hiA'' : (i : Nat) < stP.R.A.size := by
                rw [hAsize]; exact hi_m
          have hrowlen :
            (stP.R.A[(i : Nat)]'hiA'').size = n := by
            have := stP.R.rect (i : Nat) hiA''
            simpa using this
          have : stP.R.A[k].size = n := by
            have : k < stP.R.A.size := by
              conv at hk_lt_mSz =>
                unfold mSz
              exact hk_lt_mSz
            simp [stP.R.rect k hk_lt_mSz]
          rw [this]
          unfold c at hc
          exact hc
        ) = 0
        · -- 1. a = 0 の場合：ループは k+1 に進むので IH を使う
          have hk1_row : stP.rowCount ≤ k + 1 := by
            have : k ≤ k+1 := Nat.le_succ k
            exact le_trans hk_row this

          have hk1_le_i : k + 1 ≤ (i : Nat) := Nat.succ_le_of_lt hk_lt_i

          -- i - (k+1) = d を hk_d から導く
          have hk_d' : (i : Nat) - (k+1) = d := by
            -- 標準補題 Nat.sub_succ を使う
            -- i - (k+1) = (i - k) - 1 = succ d - 1 = d
            have := hk_d
            -- i - (k+1) = i - k - 1
            calc
              (i : Nat) - (k+1)
                  = ((i : Nat) - k) - 1 := by
                      rw [Nat.sub_succ]
                      simp
              _   = Nat.succ d - 1 := by simp [*]
              _   = d := by simp

          -- IH を k+1 に適用
          have ⟨i0, hi0⟩ :=
            IH (k+1) hk_d' hk1_row hk1_le_i

          -- if の else ブランチが選ばれることを `simp` に教える
          have hz' :
            stP.R.A[k][stP.colPtr]'(by
              have hiA'' : (i : Nat) < stP.R.A.size := by
                rw [hAsize]; exact hi_m
              have hrowlen :
                (stP.R.A[(i : Nat)]'hiA'').size = n := by
                have := stP.R.rect (i : Nat) hiA''
                simpa using this
              have : stP.R.A[k].size = n := by
                have : k < stP.R.A.size := by
                  conv at hk_lt_mSz =>
                    unfold mSz
                  exact hk_lt_mSz
                simp [stP.R.rect k hk_lt_mSz]
              rw [this]
              unfold c at hc
              exact hc
            ) = 0 := by
            -- row = A[k] なので、a = row[c] = A[k][c]
            simp [hz]

          refine ⟨i0, ?_⟩
          simp [hz', hi0]
        · -- 2. a ≠ 0 の場合：some ⟨k, _⟩ を返す
          have hk_m : k < m := by
            have := stP.R.rowSize
            have hm : mSz = m := by simpa [mSz] using this
            simpa [hm] using hk_lt_mSz
          refine ⟨⟨k, hk_m⟩, ?_⟩
          simp [hz]

  -- 実際に使うのは k = rowCount, d = i - rowCount のケース
  have hRow_le : stP.rowCount ≤ (i : Nat) := hi_ge
  have hRow_dist : (i : Nat) - stP.rowCount = (i : Nat) - stP.rowCount := rfl
  obtain ⟨i0, hi0_some⟩ :=
    aux ((i : Nat) - stP.rowCount) stP.rowCount hRow_dist (le_rfl) hRow_le
  exact ⟨i0, hi0_some⟩

lemma findPivot_loop_some_sound
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K) (hcol : stP.colPtr < n)
  {k : Nat} {i0 : Fin m}
  (h : findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0) :
  (stP.rowCount : Nat) ≤ i0 ∧
  (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ ≠ 0 := by
  classical
  let mSz := stP.R.A.size

  -- 「残り行数 d = mSz - k」で再帰
  have aux :
    ∀ d k,
      mSz - k = d →
      findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0 →
      (stP.rowCount : Nat) ≤ i0 ∧
      (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ ≠ 0 := by
    intro d
    induction d with
    | zero =>
        intro k hk hfk
        -- d = 0 → mSz - k = 0 → k ≥ mSz
        -- でも findPivot_loop の定義を見ると、
        -- k ≥ mSz なら即 none になるので、
        -- some i0 という仮定と矛盾 → このケースは起こりえない
        have hk_ge : mSz ≤ k := Nat.le_of_sub_eq_zero hk
        unfold findPivot_loop at hfk
        -- hi : k < mSz は成り立たないので hi ブランチは潰れる
        have : ¬ k < mSz := by exact Nat.not_lt_of_ge hk_ge
        simp [mSz, this] at hfk
    | succ d IH =>
        intro k hk hfk
        -- ここからは findPivot_loop の一段分を展開して場合分け
        unfold findPivot_loop at hfk
        have hk1 : mSz - (k+1) = d := by
          -- hk : mSz - k = d + 1 から計算
          -- mSz - (k+1) = (mSz - k) - 1 = (d+1) - 1 = d
          have := hk
          calc
            mSz - (k+1)
                = (mSz - k) - 1 := by
                    -- 標準補題 Nat.sub_succ
                    simp [Nat.sub_add_eq]  -- 必要に応じて simp を調整
            _   = (d+1) - 1 := by simp [this]
            _   = d := by simp
        by_cases hi : k < mSz
        · simp [mSz, hi] at hfk
          -- rowCount ≤ k かどうか
          by_cases hrow : stP.rowCount ≤ k
          · simp [hrow] at hfk

            by_cases hz : (stP.R.A[k][stP.colPtr]'(
              by
              have : stP.R.A[k].size = n := by
                have : k < stP.R.A.size := by
                  conv at hi =>
                    unfold mSz
                  exact hi
                simp [stP.R.rect k this]
              rw [this]
              exact hcol
            )) = 0
            · -- 2. a = 0 の場合
              have hfk' := hfk
              simp [hz] at hfk'  -- ⇒ hfk' : findPivot_loop ... (k+1) = some i0

              -- k+1 に対して IH を使う準備（mSz - (k+1) = d を hk から出す）


              -- IH を (k+1) に適用
              exact IH (k+1) hk1 hfk'
            · -- 1. a ≠ 0 の場合
              simp [hz] at hfk

              -- hfk : some i0 = some ⟨k, _⟩ なので i0 = ⟨k, _⟩ を取り出す
              have hi0_eq : i0 = ⟨k,by
                have : k = i0.val := by simp [hfk.symm]
                rw [this]
                exact i0.is_lt
              ⟩ := hfk.symm
              have hk_i0_eq : k = (i0 : Nat) := by
                  simp [hi0_eq]
              -- rowCount ≤ k は hrow から直接
              have h_rowCount_le_i0 : (stP.rowCount : Nat) ≤ i0 := by
                rw [hk_i0_eq] at hrow
                exact hrow
              have hk_m : k < m := by
                have := stP.R.rowSize
                have hm : mSz = m := by simpa [mSz] using this
                simpa [hm] using hi
              have h_get :
                (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ =
                  stP.R.A[k][stP.colPtr]'(
                    by
                      have : stP.R.A[k].size = n := by
                        have : k < stP.R.A.size := by
                          conv at hi => unfold mSz
                          exact hi
                        simp [stP.R.rect k this]
                      rw [this]
                      exact hcol
                  ) := by
                  simp [hi0_eq]
                -- 既に使っている `matOf_entry_eq_get` を流用
                -- （i := k, c := stP.colPtr）
                  apply (matOf_entry_eq_get (R := stP.R)
                    (i := k) (c := stP.colPtr) hcol (hi := hk_m))
              -- matOf stP.R i0 col ≠ 0 も hne から直接
              have h_matOf_nz :
                (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ ≠ 0 := by
                intro hzero
                apply hz
                simp [hi0_eq] at hzero
                exact hzero

              exact ⟨h_rowCount_le_i0, h_matOf_nz⟩
          · -- hrow が偽（rowCount ≤ k が成り立たない）なら、
            -- この step では「そのまま findPivot_loop ... (k+1)」を呼んでいるので、
            -- again hfk を IH に渡せる。
            have hk_lt_row : k < stP.rowCount := Nat.lt_of_not_ge hrow
            -- hi から k+1 < mSz もわかるので、
            -- mSz - (k+1) = d を hk から計算して IH に渡す。
            have hk_lt_row_neg : ¬ (stP.rowCount ≤ k) := by exact Nat.not_le_of_lt hk_lt_row
            simp [hrow] at hfk
            exact IH (k+1) hk1 hfk

        · -- hi が成り立たない (¬ k < mSz) なら、この step でも none で終わるはず。
          -- でも hfk は some i0 なので矛盾。
          simp [mSz, hi] at hfk

  -- 実際に使いたいのは k = 任意（特に rowCount）なので、
  -- d := mSz - k をとって aux を呼べばよい。
  have hk : mSz - k = mSz - k := rfl
  exact aux (mSz - k) k hk h

-- i = rowCount から始まるループが none を返すことと、
-- rowCount 以降で非零な行が存在しないことは同値
lemma findPivot_loop_none_iff'
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K) (hcol : stP.colPtr < n) :
  findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount = none
    ↔ ¬ HasPivotPred stP hcol := by
  classical
  constructor
  · -- → : none なら pivot は存在しない
    intro h_none h_has
    -- findPivot_loop_some_of_hasPivot から some i0 が出る
    obtain ⟨i0, h_some⟩ :=
      findPivot_loop_some_of_hasPivot stP hcol h_has
    -- しかし今は none と仮定しているので矛盾
    have : some i0 = none := by simp [h_none] at h_some
    exact Option.noConfusion this
  · -- ← : pivot が存在しないなら、ループは none
    intro h_no
    -- こちらは contrapositive を使う
    -- 「loop ≠ none → HasPivotPred」が言えれば、
    --   ¬HasPivotPred から loop = none が従う
    by_contra h_contra
    -- h_contra : findPivot_loop ... ≠ none
    -- some か none かで場合分け
    cases hopt : findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount with
    | none =>
        -- none なのに ≠ none は矛盾
        exact h_contra hopt
    | some i0 =>
        -- some i0 なら、soundness 補題から HasPivotPred が従う
        have h_sound :
          (stP.rowCount : Nat) ≤ i0 ∧
          (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ ≠ 0 :=
          findPivot_loop_some_sound stP hcol (k := stP.rowCount) (i0 := i0) hopt

        rcases h_sound with ⟨h_ge, h_nz⟩

        -- HasPivotPred は「rowCount 以上で、その列が非零な行がある」
        have h_has : HasPivotPred stP hcol :=
          ⟨i0, h_ge, h_nz⟩

        -- これは ¬HasPivotPred と矛盾
        exact h_no h_has

-- ループ結果は任意の pivot index 以下
/- 「行 j が rowCount 以上で非零なら、rowCount から始めたループはそれより後を返すことはない（最大でも j）」 -/
lemma findPivot_loop_result_le_pivot
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K) (hcol : stP.colPtr < n)
  {k : Nat} {i0 j : Fin m}
  (h_loop : findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0)
  (h_row_le_k : (stP.rowCount : Nat) ≤ k)
  (h_k_le_j : k ≤ (j : Nat))
  (h_j_nz : (matOf stP.R) j ⟨stP.colPtr, hcol⟩ ≠ 0) :
  (i0 : Nat) ≤ (j : Nat) := by
  classical
  -- 行数
  let mSz := stP.R.A.size

  -- 強い帰納法：d = j - k
  have aux :
    ∀ d k,
      (j : Nat) - k = d →
      (stP.rowCount : Nat) ≤ k →
      k ≤ (j : Nat) →
      ∀ {i0},
        findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0 →
        (i0 : Nat) ≤ (j : Nat) := by
    intro d
    induction d with
    | zero =>
        intro k hk_d hk_row hk_le i0 hfk
        -- j - k = 0 かつ k ≤ j なので k = j
        have hk_ge : (j : Nat) ≤ k := Nat.le_of_sub_eq_zero hk_d
        have hk_eq : k = (j : Nat) := Nat.le_antisymm hk_le hk_ge
        subst hk_eq   -- 以降 k = j
        -- k = j のとき、行 j は pivot なので、ループは some ⟨j, _⟩ を返すはず
        -- i0 ≤ j を示したいので、実際には i0 = j を取れればよい
        -- ここは findPivot_loop の定義を 1 段展開して `simp` でつぶす：
        unfold findPivot_loop at hfk
        have hj_lt_mSz : (j : Nat) < mSz := by
          -- stP.R.rowSize : stP.R.A.size = m を使って j < mSz を作る
          have hjm : (j : Nat) < m := j.is_lt
          have hAsize : stP.R.A.size = m := stP.R.rowSize
          simp [mSz, hAsize, hjm]   -- ← `simp` で j < mSz
        have hrow' : stP.rowCount ≤ (j : Nat) := by
          exact Nat.le_trans h_row_le_k h_k_le_j   -- もともと rowCount ≤ k ≤ j
        simp [mSz, hj_lt_mSz, hrow'] at hfk
        let c := stP.colPtr
        have hc : c < n := hcol

        -- matOf の成分と Array アクセスの一致（既に持っている補題と同じパターン）
        have h_get :
          (matOf stP.R) j ⟨c, hc⟩ =
            stP.R.A[(j : Nat)][c]'(
              by
                have : stP.R.A[(j : Nat)].size = n := by
                  have : j < stP.R.A.size := by
                    unfold mSz at hj_lt_mSz
                    exact hj_lt_mSz
                  simp [stP.R.rect j this]
                rw [this]
                exact hcol
            ) := by
          have hjA : (j : Nat) < stP.R.A.size := by
            unfold mSz at hj_lt_mSz
            exact hj_lt_mSz
          have hrowlen :
            (stP.R.A[(j : Nat)]'hjA).size = n := by
            have := stP.R.rect (j : Nat) hjA
            simpa using this
          -- 実際の書き方は環境の `matOf_entry_eq_get` に合わせてください
          simpa [c, hrowlen] using
            (matOf_entry_eq_get (R := stP.R) (i := (j : Nat))
              (hi := j.is_lt) (c := c) (hc := hc))

        -- h_j_nz : matOf stP.R j ⟨c,hc⟩ ≠ 0 から a ≠ 0 を得る
        have hne_a :
          stP.R.A[(j : Nat)][c]'(
            by
              have : stP.R.A[(j : Nat)].size = n := by
                have : j < stP.R.A.size := by
                  unfold mSz at hj_lt_mSz
                  exact hj_lt_mSz
                simp [stP.R.rect j this]
              rw [this]
              exact hcol
          ) ≠ 0 := by
          have := h_j_nz
          -- h_get で書き換え
          simpa [h_get] using this

        -- findPivot_loop 内部の a と一致させる（`simp` の都合上）
        have hne :
          stP.R.A[(j : Nat)][stP.colPtr]'(
            by
              have hjA : (j : Nat) < stP.R.A.size := by
                unfold mSz at hj_lt_mSz
                exact hj_lt_mSz
              have hrowlen :
                (stP.R.A[(j : Nat)]'hjA).size = n := by
                have := stP.R.rect (j : Nat) hjA
                simpa using this
              -- row 配列長が n であることから colPtr < n を流す
              simpa [hrowlen, c] using hc
          ) ≠ 0 := by
          -- index の証明部分が上の hne_a と同じになるので `simp` で潰す
          simpa [c] using hne_a

        -- これで if の then ブランチに入ることが分かるので、
        -- hfk から some i0 = some ⟨j,_⟩ を取り出す
        have hfk' := hfk
        simp [hne] at hfk'  -- hfk' : some i0 = some ⟨j, _⟩

        -- some の injectivity
        have hi0_eq :
          i0 = ⟨(j : Nat), j.is_lt⟩ := by
          simp [hfk'.symm]

        -- したがって i0.val = j
        have hi0_val : (i0 : Nat) = (j : Nat) := by
          simp [hi0_eq]

        -- 目標は (i0 : Nat) ≤ j なので、等式から従う
        exact le_of_eq hi0_val
    | succ d IH =>
        intro k hk_d hk_row hk_le i0 hfk
        -- ここから 1 ステップ分 findPivot_loop を展開して場合分け
        unfold findPivot_loop at hfk
        -- hi : k < mSz で場合分け
        by_cases hi : k < mSz
        · -- 行 k が範囲内
          simp [mSz, hi] at hfk
          -- rowCount ≤ k なので hrow ブランチに入る
          have hrow' : stP.rowCount ≤ k := hk_row
          simp [hrow'] at hfk
          -- a の値で場合分け
          by_cases hz : stP.R.A[k][stP.colPtr]'(
            by
            have : stP.R.A[k].size = n := by
              have : k < stP.R.A.size := by
                conv at hi =>
                  unfold mSz
                exact hi
              simp [stP.R.rect k this]
            rw [this]
            exact hcol
          ) = 0
          · -- a = 0 → ループは k+1 に進む
            have hfk' := hfk
            simp [hz] at hfk'  -- hfk' : findPivot_loop ... (k+1) = some i0
            -- j - (k+1) = d を hk_d から計算
            have hk_d' : (j : Nat) - (k+1) = d := by
              have := hk_d
              -- j - (k+1) = (j - k) - 1 = (d+1) - 1 = d
              calc
                (j : Nat) - (k+1)
                    = ((j : Nat) - k) - 1 := by
                        -- `Nat.sub_succ` を `simp` で使う
                        simp [Nat.sub_add_eq]
                _ = Nat.succ d - 1 := by simp [*]
                _ = d := by simp
            -- rowCount ≤ k+1
            have hk1_row : (stP.rowCount : Nat) ≤ k+1 :=
              Nat.le_trans hk_row (Nat.le_succ k)
            -- k+1 ≤ j
            have hk1_le : k+1 ≤ (j : Nat) :=
              Nat.succ_le_of_lt (lt_of_le_of_ne hk_le ?hne)  -- k ≠ j
            · -- k ≠ j は、もし k = j なら行 j が 0 になるが h_j_nz と矛盾
              exact IH (k+1) hk_d' hk1_row hk1_le hfk'
            · -- k ≠ j の証明
              have hk_ne : k ≠ (j : Nat) := by
                intro hk_eq
                subst hk_eq
                -- hk_d : (j - j) = succ d なので矛盾
                have hk_d0 : 0 = d + 1 := by
                  simp [] at hk_d
                have : d + 1 ≠ 0 := by simp
                exact this hk_d0.symm
              exact hk_ne
          · -- a ≠ 0 → このステップで some ⟨k, _⟩ を返す
            simp [hz] at hfk
            -- hfk : some i0 = some ⟨k, _⟩
            -- ⟨k, _⟩ の val は k
            have : (i0 : Nat) = k := by
              simp [hfk.symm]
            -- もともと k ≤ j なので i0 ≤ j
            exact le_trans (by simp [this]) hk_le
        · -- hi が成り立たない (= k ≥ mSz) のに some が返るのは矛盾
          have : ¬ k < mSz := by exact Nat.not_lt_of_ge (Nat.le_of_not_gt hi)
          simp [mSz, this] at hfk

  -- 今欲しいのは k = rowCount の場合
  have hk : (j : Nat) - k = (j : Nat) - k := rfl
  exact aux _ _ hk h_row_le_k h_k_le_j h_loop

-- ループが some i0 を返すことと、i0 が first pivot index であることは同値
lemma findPivot_loop_eq_some_iff
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K) (hcol : stP.colPtr < n) (i0 : Fin m) :
  findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount = some i0
    ↔ IsFirstPivotIndex stP hcol i0 := by
  classical
  constructor
  · -- → 方向：ループが i0 を返す ⇒ i0 は first pivot
    intro h_loop
    -- まず「pivot である」部分は soundness から
    have h_sound :=
      findPivot_loop_some_sound (stP := stP) (hcol := hcol)
        (k := stP.rowCount) (i0 := i0) h_loop
    rcases h_sound with ⟨h_ge, h_nz⟩
    -- pivot が存在するので HasPivotPred
    have h_has : HasPivotPred stP hcol := ⟨i0, h_ge, h_nz⟩

    -- findPivot_spec は none ではない
    have h_spec_ne_none :
      findPivot_spec stP hcol ≠ none := by
      intro hnone
      have h_no_pivot : ¬ HasPivotPred stP hcol :=
        (findPivot_spec_eq_none_iff stP hcol).1 hnone
      exact h_no_pivot h_has

    -- したがって some j になっている
    obtain ⟨j, h_spec⟩ :
      ∃ j : Fin m, findPivot_spec stP hcol = some j := by
        cases hspec : findPivot_spec stP hcol with
        | none =>
            exfalso
            exact h_spec_ne_none hspec
        | some j =>
            exact ⟨j, rfl⟩

    -- spec 側の補題で j が first pivot index
    have hFirst_j :
      IsFirstPivotIndex stP hcol j :=
      (findPivot_spec_eq_some_iff stP hcol j).1 h_spec

    -- j ≤ i0 （first なので全ての pivot index 以下）
    have h_j_le_i0 : (j : Nat) ≤ (i0 : Nat) := by
      -- IsFirstPivotIndex の定義から rowCount ≤ i0, 非零なので、
      -- 「FirstPivot は任意の pivot index 以下」という補題を作って使う
      rcases hFirst_j with ⟨hj_ge, hj_nz, hj_zero_before⟩
      -- i0 が pivot index であることを使って矛盾から `¬ i0 < j` を出す
      by_contra hlt
      have hzero :
        (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ = 0 := by
        have : i0 < j := lt_of_not_ge hlt
        exact hj_zero_before i0 h_ge this
      exact h_nz hzero

    -- i0 ≤ j （ループはどの pivot index j に対しても i0 ≤ j）
    have h_i0_le_j : (i0 : Nat) ≤ (j : Nat) :=
      findPivot_loop_result_le_pivot
        (stP := stP) (hcol := hcol)
        (k := stP.rowCount) (i0 := i0) (j := j)
        h_loop (le_rfl)  -- rowCount ≤ rowCount
        (by exact hFirst_j.1) -- rowCount ≤ j
        (by exact hFirst_j.2.1) -- non-zero at j

    -- 2 つの不等式から Nat 値の等式
    have h_eq_nat : (i0 : Nat) = (j : Nat) :=
      le_antisymm h_i0_le_j h_j_le_i0

    -- Fin.ext で i0 = j
    have h_eq_fin : i0 = j := by
      apply Fin.ext
      exact h_eq_nat

    -- j が first pivot index なので、i0 も first pivot index
    simpa [h_eq_fin] using hFirst_j

  · -- ← 方向：first pivot index ならループは i0 を返す
    intro hFirst
    -- ここは「rowCount から i0 まで強い帰納法で走査して、
    --   前は全部 0, i0 で初めて ≠0 だから some i0 が返る」
    -- という補題を作って使うときれいに書けます。

    have h_ge : (stP.rowCount : Nat) ≤ i0 := hFirst.1
    have h_nz : (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ ≠ 0 := hFirst.2.1
    have h_zero_before := hFirst.2.2

    -- さきほど `findPivot_loop_some_of_hasPivot` を証明したときと同じ形で、
    -- d := i0 - k による強い帰納法で
    --   「rowCount ≤ k ≤ i0 → findPivot_loop ... k = some i0」
    -- を示し、それを k = rowCount に適用します。

    -- （ここは少し長くなるのでスケルトンだけ）
    have aux :
      ∀ d k,
        (i0 : Nat) - k = d →
        stP.rowCount ≤ k →
        k ≤ (i0 : Nat) →
        findPivot_loop stP.R stP.rowCount stP.colPtr hcol k = some i0 := by
      intro d
      induction d with
      | zero =>
          -- d = 0 → k = i0 の場合：一段展開して a ≠ 0 のブランチに入る
          intro k hk_d hk_row hk_le
          -- i0 - k = 0 なので i0 ≤ k
          have hi0_le_k : (i0 : Nat) ≤ k := Nat.le_of_sub_eq_zero hk_d
          -- k ≤ i0 と合わせて k = i0
          have hk_eq : k = (i0 : Nat) := Nat.le_antisymm hk_le hi0_le_k
          subst hk_eq
          -- 以降 k = i0

          -- i0 行は配列範囲内
          have hi0A : (i0 : Nat) < stP.R.A.size := by
            have := stP.R.rowSize
            have hAsize : stP.R.A.size = m := this
            simp [hAsize]

          -- findPivot_loop を 1 ステップ展開
          unfold findPivot_loop
          -- k = i0 なので hi0A, h_ge で if を 2 段潰す
          simp [hi0A, h_ge]  -- goal: (if h : a = 0 then _ else some ⟨i0,_⟩) = some i0

          -- あとは h_nz から「a ≠ 0」、すなわち else ブランチを選ぶことを示せばよい
          -- ここで `a` を matOf の成分に結び付ける
          have h_get :
            (matOf stP.R) i0 ⟨stP.colPtr, hcol⟩ =
              stP.R.A[i0.val][stP.colPtr]'(
                by
                  have : stP.R.A[i0.val].size = n := by
                    simp [stP.R.rect i0.val hi0A]
                  rw [this]
                  exact hcol
              ) := by
            -- ここは以前の補題と全く同じパターン：
            -- `matOf_entry_eq_get` を使って書けます。
            -- 既に書いたものをコピペしてください。
            -- 例:
            -- have hi0A' : (i0 : Nat) < stP.R.A.size := by
            --   simpa [mSz, hAsize] using hi0_m
            exact matOf_entry_eq_get (R := stP.R)
              (i := i0.val) (hi := by simp) (c := stP.colPtr) (hc := hcol)


          have hne_a :
            stP.R.A[i0.val][stP.colPtr]'(
              by
                have : stP.R.A[i0.val].size = n := by
                  simp [stP.R.rect i0.val hi0A]
                rw [this]
                exact hcol
            ) ≠ 0 := by
            have := h_nz
            simpa [h_get] using this

          -- findPivot_loop 内部での index 証明を整えて `simp` できる形にする
          have hne :
            stP.R.A[i0.val][stP.colPtr]'(
              by
                have : stP.R.A[i0.val].size = n := by
                  simp [stP.R.rect i0.val hi0A]
                rw [this]
                exact hcol
            ) ≠ 0 := by
            -- index 証明が同じなので `simp` で hne_a に落とす
            simpa using hne_a

          -- これで if の else ブランチが選ばれる
          -- simp のゴールは `by_cases` の中なので：
          intro hz
          exact (hne hz).elim
      | succ d IH =>
          -- d+1 → k < i0 の場合：行 k の成分は 0 なので (k+1) に進み、IH を適用
          intro k hk_d hk_row hk_le
          -- まず k < i0 を取る（もし k = i0 なら d = 0 のはず）
          have hk_ne_i0 : k ≠ (i0 : Nat) := by
            intro hk_eq
            subst hk_eq
            simp at hk_d
          have hk_lt_i0 : k < (i0 : Nat) :=
            lt_of_le_of_ne hk_le hk_ne_i0

          -- k < mSz
          have hk_lt_mSz : k < stP.R.A.size := by
            have hAsize : stP.R.A.size = m := stP.R.rowSize
            simp [hAsize]
            exact Nat.lt_trans hk_lt_i0 i0.is_lt

          -- findPivot_loop を一段展開
          unfold findPivot_loop
          -- 範囲内 & rowCount ≤ k なので外側 2 段の if を潰す
          simp [hk_lt_mSz, hk_row]

          -- 行 k の列成分 a は 0 のはず（first pivot の前は全部 0）
          -- まず Fin を作る
          have hk_m : k < m := by
            exact lt_trans hk_lt_i0 i0.is_lt
          have hzero_matOf :
            (matOf stP.R) ⟨k, hk_m⟩ ⟨stP.colPtr, hcol⟩ = 0 :=
            h_zero_before ⟨k, hk_m⟩ hk_row hk_lt_i0

          -- これを Array 側に運んで、a = 0 を得る
          have hz :
            stP.R.A[k][stP.colPtr]'(
              by
                have : stP.R.A[k].size = n := by
                  simp [stP.R.rect k hk_lt_mSz]
                rw [this]
                exact hcol
            ) = 0 := by
            -- `hzero_matOf` と `matOf_entry_eq_get` から simpa
            exact by
              have h_get :
                (matOf stP.R) ⟨k, hk_m⟩ ⟨stP.colPtr, hcol⟩ =
                  stP.R.A[k][stP.colPtr]'(
                    by
                      have : stP.R.A[k].size = n := by
                        simp [stP.R.rect k hk_lt_mSz]
                      rw [this]
                      exact hcol
                  ) := by
                -- 既に使っている `matOf_entry_eq_get` を流用
                -- （i := k, c := stP.colPtr）
                  apply (matOf_entry_eq_get (R := stP.R)
                    (i := k) (c := stP.colPtr) hcol (hi := hk_m))
              simpa [h_get] using hzero_matOf

          -- `a = 0` なので、if の then ブランチで (k+1) に進む
          have hk_d' : (i0 : Nat) - (k+1) = d := by
            -- hk_d : i0 - k = d+1 から
            -- i0 - (k+1) = (i0 - k) - 1 = (d+1) - 1 = d
            have := hk_d
            calc
              (i0 : Nat) - (k+1)
                  = ((i0 : Nat) - k) - 1 := by
                      -- `Nat.sub_succ` などを使って `simp` で潰せます
                      simp [Nat.sub_add_eq]
              _ = Nat.succ d - 1 := by simp [this]
              _ = d := by simp

          have hk1_row : stP.rowCount ≤ k+1 :=
            Nat.le_trans hk_row (Nat.le_succ k)
          have hk1_le_i0 : k+1 ≤ (i0 : Nat) :=
            Nat.succ_le_of_lt hk_lt_i0

          -- IH を k+1 に適用
          have h_rec :=
            IH (k+1) hk_d' hk1_row hk1_le_i0

          -- if の中身を `simp` で潰す
          simp [hz, h_rec]

    have hRow_dist :
      (i0 : Nat) - stP.rowCount = (i0 : Nat) - stP.rowCount := rfl
    have hRow_le : stP.rowCount ≤ (i0 : Nat) := h_ge

    -- k = rowCount で aux を使う
    have h_loop :=
      aux ((i0 : Nat) - stP.rowCount) stP.rowCount hRow_dist (le_rfl) hRow_le
    exact h_loop



lemma findPivot_loop_correct
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K)
  (hcol : stP.colPtr < n) :
  findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount
    = findPivot_spec stP hcol := by
  classical
  -- spec の値で場合分け
  cases hspec : findPivot_spec stP hcol with
  | none =>
      -- spec = none の場合
      have hNo :
        ¬ HasPivotPred stP hcol :=
        (findPivot_spec_eq_none_iff (st := stP) (hcol := hcol)).1 hspec
      -- exec(loop) も none になることを示す
      have hExecNone :
        findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount = none :=
        (findPivot_loop_none_iff' stP hcol).2 hNo
      simp [hExecNone]
  | some i0 =>
      -- spec = some i0 の場合
      have hFirst :
        IsFirstPivotIndex stP hcol i0 :=
        (findPivot_spec_eq_some_iff (st := stP) (hcol := hcol) (i0 := i0)).1 hspec
      have hExecSome :
        findPivot_loop stP.R stP.rowCount stP.colPtr hcol stP.rowCount = some i0 :=
        (findPivot_loop_eq_some_iff (stP := stP) (hcol := hcol) (i0 := i0)).2 hFirst
      simp [hExecSome]



lemma findPivot_exec_eq_spec
  {m n K} [Field K] [DecidableEq K] (stP : GEStateP m n K) (hcol : stP.colPtr < n) :
  findPivot_exec (erase stP) hcol = findPivot_spec stP hcol := by
  -- erase しても R, rowCount, colPtr は同じなので simp で潰れる
  simp [findPivot_exec, erase, findPivot_loop_correct stP hcol]


lemma findPivot_exec_eq_none_iff
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K)
  (hcol : stP.colPtr < n) :
  findPivot_exec (erase stP) hcol = none
    ↔ ¬ HasPivotPred stP hcol := by
  classical
  -- exec と spec の一致
  have hspec := findPivot_exec_eq_spec (stP := stP) (hcol := hcol)

  constructor
  · -- → : exec = none → spec = none → pivot なし
    intro h_none
    -- exec = none を spec = none に書き換え
    have h_spec_none : findPivot_spec stP hcol = none := by
      simpa [hspec] using h_none
    -- spec の none 判定補題から HasPivotPred の否定へ
    exact (findPivot_spec_eq_none_iff stP hcol).1 h_spec_none

  · -- ← : pivot なし → spec = none → exec = none
    intro h_no
    have h_spec_none : findPivot_spec stP hcol = none :=
      (findPivot_spec_eq_none_iff stP hcol).2 h_no
    -- spec = none を exec = none に戻す
    simpa [hspec] using h_spec_none


-- lemma loop_none_iff
--   (stE : GEExecState m n K)
--   (hcol : stE.colPtr < n)
--   (i : Nat) :
--   loop stE hcol i = none
--     ↔ ¬ ∃ iF : Fin m, (stE.rowCount : Nat) ≤ iF ∧ (iF.val ≥ i) ∧
--         (matOf stE.R) iF ⟨stE.colPtr, hcol⟩ ≠ 0 := by
--         admit

/- 非零な行である soundness -/
lemma findPivot_exec_some_sound
  {m n K} [Field K] [DecidableEq K]
  {stE : GEExecState m n K} {j0 : Fin m}
  (hcol : stE.colPtr < n)
  (h : findPivot_exec stE hcol = some j0) :
  (stE.rowCount : Nat) ≤ j0 ∧
  (matOf stE.R) j0 ⟨stE.colPtr, hcol⟩ ≠ 0 := by
  admit

/- 非零な行のうち、最小のものを取ってくる -/
lemma findPivot_exec_some_minimal
  {m n K} [Field K] [DecidableEq K]
  {stE : GEExecState m n K} {j0 : Fin m}
  (hcol : stE.colPtr < n)
  (h : findPivot_exec stE hcol = some j0) :
  ∀ i : Fin m,
    (stE.rowCount : Nat) ≤ i →
    i.val < j0.val →
    (matOf stE.R) i ⟨stE.colPtr, hcol⟩ = 0 := by
  admit

/- find pivot の理論版と実行版の橋渡し -/

lemma findPivot_spec_vs_exec
  {m n K} [Field K] [DecidableEq K]
  (stP : GEStateP m n K)
  (hcol : stP.colPtr < n) :
  match findPivot_spec stP hcol, findPivot_exec (erase stP) hcol with
  | none, none       => True
  | some i0, some j0 => i0.val = j0.val
  | _, _             => False := by
  classical
  -- 共通の「pivot が存在するか？」述語
  let P : Prop := HasPivotPred stP hcol

  -- spec 側の none 判定
  have hNone_spec :
    findPivot_spec stP hcol = none ↔ ¬ P :=
    findPivot_spec_eq_none_iff stP hcol

  -- exec 側の none 判定（これを別補題で証明しておく）
  have hNone_exec :
    findPivot_exec (erase stP) hcol = none ↔ ¬ P :=
    findPivot_exec_eq_none_iff stP hcol

  -- pivot の有無で大きく場合分け
  by_cases hP : P
  · -- case 1: pivot が存在する
    -- → どちらも none ではないはず
    have hSpec_not_none :
      findPivot_spec stP hcol ≠ none := by
      intro hnone
      have : ¬ P := (hNone_spec.mp hnone)
      exact this hP

    have hExec_not_none :
      findPivot_exec (erase stP) hcol ≠ none := by
      intro hnone
      have : ¬ P := (hNone_exec.mp hnone)
      exact this hP

    -- ここからは、両方とも some であることを使って
    -- i0, j0 を取り出す
    rcases hSpec : findPivot_spec stP hcol with _ | i0
    · exact (hSpec_not_none hSpec).elim
    rcases hExec : findPivot_exec (erase stP) hcol with _ | j0
    · exact (hExec_not_none hExec).elim

    -- ここまで来たら goal は `i0.val = j0.val`
    -- soundness / minimality 補題を使う

    -- spec 側: some i0 のときの性質（rowCount ≤ i0 ∧ 非零）
    have hSpec_sound :=
      findPivot_spec_some_sound
        (st := stP) (i0 := i0) hcol hSpec

    -- exec 側: some j0 のときの性質（rowCount ≤ j0 ∧ 非零）
    have hExec_sound :=
      findPivot_exec_some_sound
        (stE := erase stP) (j0 := j0) hcol hExec

    -- exec 側: some j0 のときの最小性
    have hExec_min :=
      findPivot_exec_some_minimal
        (stE := erase stP) (j0 := j0) hcol hExec

    -- spec 側: i0.val が P の Nat.find になっていること
    have hSpec_idx :
      ∃ hex : P, i0.val = Nat.find (exists_of_HasPivotPred_to_ExistsPivotIndexPred stP hcol hex)
      := by
        -- ここは「findPivot_spec は Nat.find を返している」ことを
        -- formalize した補題を使うイメージ
        admit

    -- exec 側: j0.val が「rowCount 以上で最初に非零になる行」であること
    -- から、Nat.find ≤ j0.val と j0.val ≤ Nat.find を示して
    -- `Nat.le_antisymm` で等しいことを出す。
    have h_le : i0.val ≤ j0.val := by
      -- P の証人として「j0 が非零」という事実を使う → Nat.find ≤ j0.val
      admit

    have h_ge : j0.val ≤ i0.val := by
      -- 「i0 より前は全部 0」という spec/exec 合わせ技で示す
      admit
    have h_eq : i0.val = j0.val :=
      Nat.le_antisymm h_le h_ge

    -- ここまで来れば、match の some/some ブランチのゴールを満たす：
    --   i0.val = j0.val
    -- それ以外の情報は要らないので、そのまま返す
    simpa [hSpec, hExec, h_eq]

  · -- case 2: pivot が存在しない → どちらも none のはず
    have hNo : ¬ P := hP

    have hSpec_none :
      findPivot_spec stP hcol = none :=
      (hNone_spec.mpr hNo)

    have hExec_none :
      findPivot_exec (erase stP) hcol = none :=
      (hNone_exec.mpr hNo)

    -- match 式を具体化してしまう
    --   (none, none) のブランチだけ True,
    --   それ以外のブランチは False
    -- なので、このケースは True
    -- `simp` に match の定義を噛ませれば OK
    simp [hSpec_none, hExec_none]


-- ==============================
-- Invの保持補題（1ステップ）
-- ==============================

lemma inv_step_none
  {m n K} [Field K] {st : GEStateP m n K} (hcol : st.colPtr < n)
  (hnone : findPivot_spec st hcol = none)
  : Inv st.M0 st.R st.rowCount (st.colPtr + 1) st.pivot := by
  classical
  -- もとの不変量を省略記法で
  have hInv := st.inv

  refine
    { I0_rows := hInv.I0_rows
    , I0_rect := hInv.I0_rect
    , I1_bound := ?_
    , I1_mono  := hInv.I1_mono
    , I1_in    := ?_
    , I2_unit  := hInv.I2_unit
    , I3_left0 := hInv.I3_left0
    , I4_tail0 := ?_
    , I5_fac   := hInv.I5_fac
    }

  -- I1_bound : rowCount ≤ m ∧ (colPtr + 1) ≤ n
  · have hrow_le_m : st.rowCount ≤ m := hInv.I1_bound.1
    -- hcol : st.colPtr < n から succ_le_of_lt
    have hcol1_le_n : st.colPtr + 1 ≤ n := Nat.succ_le_of_lt hcol
    exact ⟨hrow_le_m, hcol1_le_n⟩

  -- I1_in : ∀ i, st.pivot i < st.colPtr + 1
  · intro i
    -- もともと st.pivot i < st.colPtr
    have hlt : (st.pivot i : Nat) < st.colPtr := hInv.I1_in i
    -- st.colPtr ≤ st.colPtr + 1 なので < を伝播
    have hle : st.colPtr ≤ st.colPtr + 1 := Nat.le_succ _
    exact Nat.lt_of_lt_of_le hlt hle

  -- I4_tail0 : 新しい c0 = st.colPtr + 1 に対する tail-zero 条件
  · intro j hj_lt hnoPivot i' hi_ge
    -- hj_lt : (j : ℕ) < st.colPtr + 1 から
    -- (j : ℕ) < st.colPtr ∨ (j : ℕ) = st.colPtr に分岐
    have hj_cases :
      (j : Nat) < st.colPtr ∨ (j : Nat) = st.colPtr := by
      -- lt_succ_iff : a < b+1 ↔ a < b ∨ a = b
      exact Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hj_lt)

    cases hj_cases with
    | inl hj_lt_old =>
        -- 1. j < st.colPtr の場合は元の I4_tail0 がそのまま使える
        exact hInv.I4_tail0 j hj_lt_old hnoPivot i' hi_ge

    | inr hj_eq =>
        -- 2. j = st.colPtr の場合：
        --    - pivot の列にはなっていない（元々 p i < colPtr なので当然）
        --    - findPivot_spec が none なので rowCount 以降はこの列が全部 0
        -- まず j が Fin として ⟨st.colPtr, hcol⟩ と等しいことを作る
        have hj_fin_eq : j = ⟨st.colPtr, hcol⟩ := by
          apply Fin.ext
          -- 値レベルの等式は hj_eq
          simp [hj_eq]

        -- findPivot_spec_none_sound から「rowCount 以降は 0」
        have hz :=
          findPivot_spec_none_sound (st := st) (hcol := hcol) hnone i' hi_ge
        -- hz : (matOf st.R) i' ⟨st.colPtr, hcol⟩ = 0
        -- これを j についての等式に書き換える
        simpa [hj_fin_eq] using hz

lemma matOf_rSwap_row_left
  {m n K} [Field K]
  (R : Rectified m n K)
  {i j : Nat} (hi : i < m) (hj : j < m)
  (c : Fin n) :
  (matOf (rSwap R i j)) ⟨i, hi⟩ c
    = (matOf R) ⟨j, hj⟩ c := by
  -- A.size = m
  have hAsize : R.A.size = m := R.rowSize
  have hiA : i < R.A.size := by simpa [hAsize] using hi
  have hjA : j < R.A.size := by simpa [hAsize] using hj

  -- 左辺を配列アクセスに書き換え
  have hL :=
    matOf_entry_eq_get
      (R := rSwap R i j)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := i) (hi := hi)

  -- 右辺も配列アクセスに書き換え
  have hR :=
    matOf_entry_eq_get
      (R := R)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := j) (hi := hj)

  -- これで
  -- hL :
  --   (matOf (rSwap R i j)) ⟨i, hi⟩ c
  --     = (rSwap R i j).A[i]'(…)[(c : Nat)]'(…)
  -- hR :
  --   (matOf R) ⟨j, hj⟩ c
  --     = R.A[j]'(…)[(c : Nat)]'(…)

  -- 行の入れ替えが「行レベル」でどうなっているかの補題を使う
  have hRow :
    (rSwap R i j).A[i]'(
      by
        -- i < (rSwap R i j).A.size
        have : (rSwap R i j).A.size = m :=
          (rSwap R i j).rowSize
        simpa [this] using hi
    ) = R.A[j] := by
    -- これは rSwap の定義と swapRows の補題から出す
    -- （swapRows_get_left みたいな補題を別途用意しておく）
    -- イメージ：
    -- unfold rSwap
    -- have hij : i < R.A.size ∧ j < R.A.size := ⟨hiA, hjA⟩
    -- simp [rSwap, hij, swapRows, hij]    -- ここで row i が row j になる
    unfold rSwap
    have hij : i < R.A.size ∧ j < R.A.size := ⟨hiA, hjA⟩
    -- ここで swapRows の補題を使う
    -- swapRows_get_left : ∀ R i j hij,
    --   (swapRows R i j hij).A[i] = R.A[j]
    have hswap := swapRows_get_left R.A hij.1 hij.2
    simp [hij, hswap]


  -- すると、行を表す Array の等式 hRow を使って、成分レベルでの等式が分かる
  have c_lt_swap_R_size : (c : Nat) < ((rSwap R i j).A[i]'(
      by
        -- i < (rSwap R i j).A.size
        have : (rSwap R i j).A.size = m :=
          (rSwap R i j).rowSize
        simpa [this] using hi
    )).size := by
    -- これは行のサイズが n であることから分かる
    have hiA' : i < (rSwap R i j).A.size := by
      have : (rSwap R i j).A.size = m :=
        (rSwap R i j).rowSize
      simpa [this] using hi
    have hrowlen :
      ((rSwap R i j).A[i]'hiA').size = n := by
      have := (rSwap R i j).rect i hiA'
      simpa using this
    have : (c : Nat) < ((rSwap R i j).A[i]'hiA').size := by
      -- ここは今のままで OK（`(c : Nat)` 自体は普通の式）
      simp [hrowlen]
    exact this
  have c_lt_R_size : (c : Nat) < (R.A[j]'(
      by
        -- j < R.A.size
        simpa [hAsize] using hj
    )).size := by
    -- これは行のサイズが n であることから分かる
    have hjA' : j < R.A.size := by
      simpa [hAsize] using hj
    have hrowlen : (R.A[j]'hjA').size = n := by
      have := R.rect j hjA'
      simpa using this
    have : (c : Nat) < (R.A[j]'hjA').size := by
      simp [hrowlen]
    exact this

  let swapedRow := (rSwap R i j).A[i]'(
      by
        -- i < (rSwap R i j).A.size
        have : (rSwap R i j).A.size = m :=
          (rSwap R i j).rowSize
        simpa [this] using hi
    )

  have hEntries :
    swapedRow[c.val] =
    R.A[j][c.val] := by
    -- あとは swapRows の「行 i が行 j に等しい」という補題から
    -- その行の c 成分が等しいことを引き出す
    -- simp [swapRows, ...] か、congrArg で行ベクトルの等式から成分の等式を取る
    unfold swapedRow
    -- swapRows_get_left で行ベクトルの等式を取る
    have hij : i < R.A.size ∧ j < R.A.size := ⟨hiA, hjA⟩
    have hswap := swapRows_get_left R.A hij.1 hij.2
    unfold rSwap
    simp [hij, hswap]


  -- 右辺・左辺それぞれを matOf_entry_eq_get で書き換えたあと hEntries で結べばよい
  -- hL の右辺を hEntries で R 側に書き換え、hR と比較
  -- 具体的には：
  --   have hL' := hL.trans ?something
  --   ...
  -- ですが、だいたい次の一行でいけることが多い：
  have hL' : (matOf (rSwap R i j)) ⟨i, hi⟩ c =
    R.A[j][c.val] := by
    -- hL で左辺を配列表現にしてから hEntries で右辺を書き換える
    --   hL : LHS = Larr
    --   hEntries : Larr = Rarr
    -- なので trans でつなぐ
    exact hL.trans hEntries

  -- 最後に hR で matOf R の成分に戻す
  -- hR.symm : Rarr = RHS なので trans
  --   LHS = Rarr かつ Rarr = RHS
  have := hL'.trans hR.symm
  -- これがちょうど求める等式
  exact this

lemma matOf_rSwap_row_right
  {m n K} [Field K]
  (R : Rectified m n K)
  {i j : Nat} (hi : i < m) (hj : j < m)
  (c : Fin n) :
  (matOf (rSwap R i j)) ⟨j, hj⟩ c
    = (matOf R) ⟨i, hi⟩ c := by
  -- A.size = m
  have hAsize : R.A.size = m := R.rowSize
  have hiA : i < R.A.size := by simpa [hAsize] using hi
  have hjA : j < R.A.size := by simpa [hAsize] using hj

  -- 左辺を配列アクセスに書き換え
  have hL :=
    matOf_entry_eq_get
      (R := rSwap R i j)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := j) (hi := hj)

  -- 右辺も配列アクセスに書き換え
  have hR :=
    matOf_entry_eq_get
      (R := R)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := i) (hi := hi)

  -- これで
  -- hL :
  --   (matOf (rSwap R i j)) ⟨i, hi⟩ c
  --     = (rSwap R i j).A[i]'(…)[(c : Nat)]'(…)
  -- hR :
  --   (matOf R) ⟨j, hj⟩ c
  --     = R.A[j]'(…)[(c : Nat)]'(…)

  -- 行の入れ替えが「行レベル」でどうなっているかの補題を使う
  have hRow :
    (rSwap R i j).A[j]'(
      by
        -- i < (rSwap R i j).A.size
        have : (rSwap R i j).A.size = m :=
          (rSwap R i j).rowSize
        simpa [this] using hj
    ) = R.A[i] := by
    -- これは rSwap の定義と swapRows の補題から出す
    -- （swapRows_get_left みたいな補題を別途用意しておく）
    -- イメージ：
    -- unfold rSwap
    -- have hij : i < R.A.size ∧ j < R.A.size := ⟨hiA, hjA⟩
    -- simp [rSwap, hij, swapRows, hij]    -- ここで row i が row j になる
    unfold rSwap
    have hij : i < R.A.size ∧ j < R.A.size := ⟨hiA, hjA⟩
    -- ここで swapRows の補題を使う
    -- swapRows_get_left : ∀ R i j hij,
    --   (swapRows R i j hij).A[i] = R.A[j]
    have hswap := swapRows_get_right R.A hij.1 hij.2
    simp [hij, hswap]

  simp [hL, hRow, hR.symm]

-- 「swap でいじってない行はそのまま」
lemma matOf_rSwap_row_other
  {m n K} [Field K]
  (R : Rectified m n K)
  {i j k : Nat} (hi : i < m) (hj : j < m) (hk : k < m)
  (hki : k ≠ i) (hkj : k ≠ j)
  (c : Fin n) :
  matOf (rSwap R i j) ⟨k, hk⟩ c =
    matOf R ⟨k, hk⟩ c := by
  -- A.size = m
  have hAsize : R.A.size = m := R.rowSize
  have hiA : i < R.A.size := by simpa [hAsize] using hi
  have hjA : j < R.A.size := by simpa [hAsize] using hj
  have hkA : k < R.A.size := by simpa [hAsize] using hk
  -- 左辺を配列アクセスに書き換え
  have hL :=
    matOf_entry_eq_get
      (R := rSwap R i j)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := k) (hi := hk)
  -- 右辺も配列アクセスに書き換え
  have hR :=
    matOf_entry_eq_get
      (R := R)
      (c := (c : Nat)) (hc := c.is_lt)
      (i := k) (hi := hk)
  simp [hL, hR]
  unfold rSwap
  simp [hiA, hjA, swapRows, Array.setIfInBounds,
  Array.getElem_set, hkj.symm, hki.symm]

/- rSwap は行入れ替え行列（permutation matrix）を左から掛けたのと同じ -/
lemma matOf_rSwap_eq_P_mul
  {m n K} [Field K]
  (R : Rectified m n K) (i j : Nat)
  (hi : i < m) (hj : j < m) :
  ∃ P : Matrix (Fin m) (Fin m) K,
    IsUnit P ∧
    matOf (rSwap R i j) = Matrix.mulᵣ P (matOf R) := by
  classical
  -- Fin インデックスに持ち上げる
  let i' : Fin m := ⟨i, hi⟩
  let j' : Fin m := ⟨j, hj⟩
  -- i', j' を入れ替える置換
  let σ : Equiv.Perm (Fin m) := Equiv.swap i' j'
  -- その permutation matrix
  let P : Matrix (Fin m) (Fin m) K := Equiv.Perm.permMatrix K σ
  refine ⟨P, ?_, ?_⟩

  · -- P は unit
    -- （実際には `Matrix.isUnit_perm` 的な補題を使う）
    have P_det : P.det ≠ 0 := by
      unfold P
      simp [Matrix.det_permutation]
      simp [σ]
      by_cases hij : i' = j'
      · -- i' = j' の場合、恒等置換なので det = 1
        simp [hij]
      · -- i' ≠ j' の場合、swap なので det = -1
        simp [hij]
    -- det ≠ 0 から isUnit を出す補題を使う
    have P_det_unit : IsUnit P.det := by
      -- ここはライブラリ的にある想定
      simp [P_det]
    exact (Matrix.isUnit_iff_isUnit_det P).mpr P_det_unit

  · -- エントリごとに等号を示す
    -- mulᵣ を普通の積に直してから ext
    -- mulᵣ の定義が `Matrix.mulᵣ P M = P ⬝ M` 的になっている想定
    ext r c
    -- 列 c のベクトルを v とおく
    let v : Fin m → K := fun r => matOf R r c
    have hv : (Matrix.mulᵣ P (matOf R)) r c = (P.mulVec v) r := by
      -- mulᵣ の定義を使って「左からの積＝各列に mulVec」
      -- という形に書き換える
      -- これは `simp [Matrix.mulᵣ, Matrix.mul, v, Matrix.mul_apply, Matrix.dotProduct]`
      -- のような形で落とせるはず
      simp [Matrix.mul_apply, Matrix.mulVec, v, dotProduct]

    have h_perm_vec :
      (P.mulVec v) r = v (σ.symm r) := by
      -- permMatrix_mulVec を使う
      -- だいたいこんな感じのsimpになる：
      --   simp [P, v, Equiv.Perm.permMatrix_mulVec, σ]
      have h := Matrix.permMatrix_mulVec (σ := σ) (v := v)
      -- h : P.mulVec v = fun r => v (σ.symm r)
      -- これを r に適用して終わり
      -- もしくは `simpa [P]` で一気に：
      simpa [P] using congrArg (fun f => f r) h
    -- まず右辺を permutation matrix の作用に書き換える
    have h_perm :
      Matrix.mulᵣ P (matOf R) r c
        = (matOf R) (σ.symm r) c := by
      -- ここは `simp [Matrix.mulᵣ]` と `Matrix.perm_mul` 系で
      --   (Matrix.perm σ ⬝ matOf R) r c = matOf R (σ⁻¹ r) c
      -- という形に落とす
      -- hv で mulᵣ を mulVec に書き換え、h_perm_vec を流し込む
      simpa [v] using (hv.trans h_perm_vec)

    -- 左辺：rSwap が行インデックスにどう作用するかを書く
    -- row インデックス r を Nat に壊す
    rcases r with ⟨k, hk⟩
    -- cases on k = i / j / その他
    have hiA : i < R.A.size := by simpa [R.rowSize] using hi
    have hjA : j < R.A.size := by simpa [R.rowSize] using hj

    -- σ⁻¹ の挙動：
    --   Equiv.swap i' j' の場合、
    --   σ.symm ⟨i,hi⟩ = ⟨j,hj⟩,
    --   σ.symm ⟨j,hj⟩ = ⟨i,hi⟩,
    --   その他は自分自身。
    -- この３ケースと、あなたが持っている
    --   matOf_rSwap_row_left / right / other
    -- を対応づける。

    by_cases hk_i : k = i
    · -- case k = i : r は swap 後の「左側」の行
      -- rSwap の定義側：i 行は j 行に入れ替わる
      have h_swap :
        matOf (rSwap R k j) ⟨k, hk⟩ c =
          matOf R ⟨j, hj⟩ c := by
        -- ここで `matOf_rSwap_row_left` を使う想定
        -- （ライブラリ的には自作補題）
        exact matOf_rSwap_row_left (R := R) (i := k) (j := j)
          (hi := hk) (hj := hj) (c := c)

      -- σ⁻¹ の側：swap の左は右へ
      have h_sigma :
        σ.symm ⟨k, hk⟩ = ⟨j, hj⟩ := by
        -- `Equiv.swap_apply_left` 的な補題
        simp [σ, Equiv.swap, i', j', Equiv.swapCore, hk_i]

      -- r も今は ⟨i,hi⟩ なので書き換え
      -- まとめ：左辺 = matOf R ⟨j,hj⟩ c、右辺も matOf R ⟨j,hj⟩ c
      simp [h_sigma] at h_perm
      simp [h_perm, hk_i.symm, h_swap]
    · -- case k ≠ i
      by_cases hk_j : k = j
      · -- case k = j（swap の右側）
        -- 同様に matOf_rSwap_row_right と
        -- `Equiv.swap_apply_right` で処理
        -- r = ⟨j, hj⟩
        have h_swap :
          matOf (rSwap R i j) ⟨j, hj⟩ c =
            matOf R ⟨i, hi⟩ c := by
          exact matOf_rSwap_row_right (R := R) (i := i) (j := j)
            (hi := hi) (hj := hj) (c := c)

        have h_sigma :
          σ.symm ⟨j, hj⟩ = ⟨i, hi⟩ := by
          simp [σ, i', j']  -- 今度は右側の swap パターン

        have h_perm_j :
          Matrix.mulᵣ P (matOf R) ⟨j, hj⟩ c =
            matOf R ⟨i, hi⟩ c := by
          conv at h_perm =>
            lhs
            arg 3
            simp [hk_j]
          conv at h_perm =>
            rhs
            simp [hk_j, h_sigma]
          exact h_perm

        conv =>
          lhs
          arg 2
          simp [hk_j]
        conv =>
          rhs
          arg 3
          simp [hk_j]
        conv =>
          rhs
          simp [h_perm_j]
        simp [h_swap]

      · -- case その他：swap しても変わらない行
        have h_swap_other :
          matOf (rSwap R i j) ⟨k, hk⟩ c =
            matOf R ⟨k, hk⟩ c := by
          -- ここで「swap でいじってない行はそのまま」の補題
          --   matOf_rSwap_row_other
          -- を使う
          have hi' : i < m := hi
          have hj' : j < m := hj
          exact matOf_rSwap_row_other (R := R)
            (i := i) (j := j) (k := k)
            (hi := hi') (hj := hj') (hk := hk)
            (hki := hk_i) (hkj := hk_j)
            (c := c)

        have h_sigma_other :
          σ.symm ⟨k, hk⟩ = ⟨k, hk⟩ := by
          -- swap でない点はそのまま
          simp [σ, i', j', Equiv.swap, Equiv.swapCore, hk_i, hk_j]

        have h_perm_other :
          Matrix.mulᵣ P (matOf R) ⟨k, hk⟩ c =
            matOf R ⟨k, hk⟩ c := by
          simpa [h_sigma_other] using h_perm

        conv =>
          lhs
          simp [h_swap_other]
        conv =>
          rhs
          simp [h_perm_other]

lemma inv_after_rSwap
  {m n K} [Field K] {st : GEStateP m n K} {i0 : Fin m}
  (hrow : st.rowCount ≤ i0)
  : Inv st.M0 (rSwap st.R st.rowCount i0.val)
      st.rowCount st.colPtr st.pivot := by
  set R' := rSwap st.R st.rowCount i0.val with hR'
  let hInv := st.inv
  -- rowCount < m （あとで Fin を作るのに使う）
  have h_row_lt_m : st.rowCount < m :=
    lt_of_le_of_lt hrow i0.is_lt
  refine
    { I0_rows := ?_
    , I0_rect := ?_
    , I1_bound := ?_
    , I1_mono  := ?_
    , I1_in    := ?_
    , I2_unit  := ?_
    , I3_left0 := ?_
    , I4_tail0 := ?_
    , I5_fac   := ?_
    }
  · -- I0_rows
    -- rSwap の定義より R' も m×n の Rectified
    simpa [R'] using (rSwap st.R st.rowCount i0.val).rowSize

  · -- I0_rect
    simpa [R'] using (rSwap st.R st.rowCount i0.val).rect
  · -- I1_bound
    have hrow_le_m : st.rowCount ≤ m := hInv.I1_bound.1
    have hcol_le_n : st.colPtr ≤ n := hInv.I1_bound.2
    exact ⟨hrow_le_m, hcol_le_n⟩
  · -- I1_mono
    exact hInv.I1_mono
  · -- I1_in
    intro i
    -- もとの Inv から pivot 列の上限を持ってくる
    have hlt_old : (st.pivot i : Nat) < st.colPtr := hInv.I1_in i
    -- st.colPtr ≤ st.colPtr なので伝播
    have hle : st.colPtr ≤ st.colPtr := Nat.le_refl _
    exact Nat.lt_of_lt_of_le hlt_old hle
  · -- I2_unit
    intro i
    -- もとの Inv から pivot 列の単位ベクトル性を持ってくる
    rcases hInv.I2_unit i with ⟨h_one_old, h_zero_old⟩

    -- pivot 行の Fin index
    let rowOld : Fin m := Fin.castLE hInv.I1_bound.1 i
    have h_rowOld_lt : (rowOld : ℕ) < st.rowCount := by
      -- castLE の値は i.val
      simp [rowOld]

    -- rowOld は swap 対象の st.rowCount, i0 とは違う
    have h_ne_left  : (rowOld : ℕ) ≠ st.rowCount := by
      exact ne_of_lt h_rowOld_lt
    have h_ne_right : (rowOld : ℕ) ≠ i0 := by
      -- i0 ≥ rowCount > rowOld
      have : (rowOld : ℕ) < i0 := lt_of_lt_of_le h_rowOld_lt hrow
      exact ne_of_lt this

    -- 「この行は rSwap で変わらない」という事実（全列について）
    have h_row_pres :
      ∀ j : Fin n,
        matOf R' rowOld j = matOf st.R rowOld j := by
      intro j
      have hi  : st.rowCount < m := h_row_lt_m
      have hj0 : i0.val < m    := i0.is_lt
      have hk  : (rowOld : ℕ) < m :=
        lt_trans h_rowOld_lt h_row_lt_m
      -- 上で書いた matOf_rSwap_row_other を使う
      simpa [R'] using
        matOf_rSwap_row_other (R := st.R)
          (i := st.rowCount) (j := i0.val) (k := rowOld)
          hi hj0 hk h_ne_left h_ne_right j

    refine ⟨?h_one, ?h_zero⟩
    · -- pivot 成分 = 1
      have h_eq := h_row_pres (st.pivot i)
      -- h_one_old : matOf st.R rowOld (st.pivot i) = 1
      unfold rowOld at h_eq
      simpa [h_one_old] using h_eq

    · -- 他の行は 0
      intro i' hi'_ne
      have hi_row : st.rowCount < m := h_row_lt_m
      have hi_i0  : (i0 : ℕ)     < m := i0.is_lt
      have hk     : (i' : ℕ)     < m := i'.is_lt

      -- case 1: i' = rowCount
      by_cases h_i'row : (i' : ℕ) = st.rowCount
      · -- swap 後の rowCount 行は、元の i0 行
        have h_eq :
          matOf R' ⟨st.rowCount, hi_row⟩ (st.pivot i) =
          matOf st.R ⟨i0, hi_i0⟩ (st.pivot i) := by
          simpa [R'] using
            matOf_rSwap_row_left (R := st.R)
              (i := st.rowCount) (j := i0.val)
              hi_row hi_i0 (c := st.pivot i)

        -- 元の i0 行の pivot 成分は 0（pivot 行 rowOld とは別行）
        have h_ne_rowOld_i0 :
          (⟨i0, hi_i0⟩ : Fin m) ≠ rowOld := by
          intro hEq
          have hv := congrArg (fun (x : Fin m) => (x : ℕ)) hEq
          have : (rowOld : ℕ) < (rowOld : ℕ) := by
            -- rowOld < i0 だったので，値が等しいと矛盾
            have hlt : (rowOld : ℕ) < i0 :=
              lt_of_lt_of_le h_rowOld_lt hrow
            have : (i0 : ℕ) = (rowOld : ℕ) := by
              simpa using hv
            simp [this] at hlt
          exact lt_irrefl _ this

        have hz :
          matOf st.R ⟨i0, hi_i0⟩ (st.pivot i) = 0 :=
          h_zero_old ⟨i0, hi_i0⟩ h_ne_rowOld_i0

        have : i' = ⟨st.rowCount, hi_row⟩ := by
          apply Fin.ext
          simp [h_i'row]

        simp [this, h_eq, hz]

      · -- case 2: i' ≠ rowCount
        by_cases h_i'i0 : (i' : ℕ) = i0
        · -- i' = i0 → swap 後の i0 行は元の rowCount 行

          have h_eq :
            matOf R' ⟨i0, hi_i0⟩ (st.pivot i) =
            matOf st.R ⟨st.rowCount, hi_row⟩ (st.pivot i) := by
            simpa [R'] using
              matOf_rSwap_row_right (R := st.R)
                (i := st.rowCount) (j := i0.val)
                hi_row hi_i0 (c := st.pivot i)

          -- 元の rowCount 行も pivot 行 rowOld とは別行なので 0
          have h_ne_rowOld_row :
            (⟨st.rowCount, hi_row⟩ : Fin m) ≠ rowOld := by
            intro hEq
            have hv := congrArg (fun (x : Fin m) => (x : ℕ)) hEq
            have : (rowOld : ℕ) < (rowOld : ℕ) := by
              have hlt : (rowOld : ℕ) < st.rowCount := h_rowOld_lt
              have : (st.rowCount : ℕ) = (rowOld : ℕ) := by
                simpa using hv
              simp [this] at hlt

            exact lt_irrefl _ this

          have hz :
            matOf st.R ⟨st.rowCount, hi_row⟩ (st.pivot i) = 0 :=
            h_zero_old ⟨st.rowCount, hi_row⟩ h_ne_rowOld_row

          have : i' = ⟨i0, hi_i0⟩ := by
            apply Fin.ext
            simp [h_i'i0]
          simp [this, h_eq, hz]

        · -- case 3: i' はどちらの swap 行でもない → 行そのまま
          have hki : (i' : ℕ) ≠ st.rowCount := h_i'row
          have hkj : (i' : ℕ) ≠ i0 := by
            intro h
            exact h_i'i0 (by simpa using h)

          have h_pres :
            matOf R' i' (st.pivot i) =
            matOf st.R i' (st.pivot i) := by
            simpa [R'] using
              matOf_rSwap_row_other (R := st.R)
                (i := st.rowCount) (j := i0.val) (k := i')
                hi_row hi_i0 hk hki hkj (st.pivot i)

          -- 元の R では i' ≠ pivot 行 rowOld なので 0
          have hz_old :
            matOf st.R i' (st.pivot i) = 0 :=
            h_zero_old i' (by
              -- hi'_ne : i' ≠ rowOld をそのまま使える
              exact hi'_ne
            )

          simp [h_pres, hz_old]
  · ------------------------------------------------------------------
    -- I3_left0 : pivot 行の「左側」は常に 0
    ------------------------------------------------------------------
    intro i j hj_lt
    -- 元の Inv から左側 0 をもらう
    have hz_old :
      matOf st.R (Fin.castLE hInv.I1_bound.1 i) j = 0 :=
      hInv.I3_left0 i j hj_lt

    -- さっきと同様に pivot 行は rSwap で変わらないことを使う
    let rowOld : Fin m := Fin.castLE hInv.I1_bound.1 i
    have h_rowOld_lt : (rowOld : ℕ) < st.rowCount := by
      simp [rowOld]
    have h_ne_left  : (rowOld : ℕ) ≠ st.rowCount := by
      exact ne_of_lt h_rowOld_lt
    have h_ne_right : (rowOld : ℕ) ≠ i0 := by
      have : (rowOld : ℕ) < i0 := lt_of_lt_of_le h_rowOld_lt hrow
      exact ne_of_lt this
    have hi  : st.rowCount < m := h_row_lt_m
    have hj0 : i0.val     < m := i0.is_lt
    have hk  : (rowOld : ℕ) < m :=
      lt_trans h_rowOld_lt h_row_lt_m

    have h_row_pres :
      matOf R' rowOld j = matOf st.R rowOld j := by
      simpa [R'] using
        matOf_rSwap_row_other (R := st.R)
          (i := st.rowCount) (j := i0.val) (k := rowOld)
          hi hj0 hk h_ne_left h_ne_right j

    -- 目標の行インデックス Fin.castLE ... i は rowOld と定義的に同じ
    have hz_old' : matOf st.R rowOld j = 0 := by
      simpa [rowOld] using hz_old

    calc
      matOf R' (Fin.castLE hInv.I1_bound.1 i) j
          = matOf R' rowOld j := by rfl
      _   = matOf st.R rowOld j := h_row_pres
      _   = 0 := hz_old'

  · ------------------------------------------------------------------
    -- I4_tail0 : まだ pivot になっていない列 j < c0 では、
    --            行 r0 以降はすべて 0
    ------------------------------------------------------------------
    intro j hj_lt h_noPivot i' hi'_ge
    -- まず「元の Inv では tail 行は全部 0」という事実を、
    --   * rowCount 行
    --   * i0 行
    --   * 一般の i' 行
    -- について用意しておく
    have hi_row : st.rowCount < m := h_row_lt_m
    have hi_i0  : (i0 : Nat) < m := i0.is_lt
    have hk     : (i' : Nat) < m := i'.is_lt

    -- 元の rowCount 行の 0
    have hz_rowCount :
      matOf st.R ⟨st.rowCount, hi_row⟩ j = 0 :=
      hInv.I4_tail0 j hj_lt h_noPivot
        ⟨st.rowCount, hi_row⟩
        (by exact le_rfl)

    -- 元の i0 行の 0 （hrow : rowCount ≤ i0 を使う）
    have hz_i0 :
      matOf st.R ⟨i0, hi_i0⟩ j = 0 :=
      hInv.I4_tail0 j hj_lt h_noPivot
        ⟨i0, hi_i0⟩
        (by
          -- (st.rowCount : Nat) ≤ (⟨i0, hi_i0⟩ : Fin m : Nat) は
          -- simp で hrow に帰着できる
          simpa using hrow)

    -- 一般の i' 用：rowCount ≤ i' という仮定 hi'_ge から 0
    have hz_old_general :
      matOf st.R i' j = 0 :=
      hInv.I4_tail0 j hj_lt h_noPivot i' hi'_ge

    -- ここから swap がどう影響するかで場合分け
    by_cases h_i'row : (i' : Nat) = st.rowCount
    · ----------------------------------------------------------------
      -- case 1: i' = rowCount
      ----------------------------------------------------------------
      -- rSwap 後の rowCount 行は「元の i0 行」
      have h_eq :
        matOf R' ⟨st.rowCount, hi_row⟩ j =
          matOf st.R ⟨i0, hi_i0⟩ j := by
        -- row_left を使う
        have := matOf_rSwap_row_left
          (R := st.R)
          (i := st.rowCount) (j := i0.val)
          hi_row hi_i0 (c := j)
        -- R' = rSwap st.R ... という定義を展開
        simpa [R'] using this

      have : i' = ⟨st.rowCount, hi_row⟩ := by
        apply Fin.ext
        simp [h_i'row]
      -- 元の i0 行は 0 だったので、その値を引き継ぐ
      simp [this, h_eq, hz_i0]

    · ----------------------------------------------------------------
      -- case 2: i' ≠ rowCount
      ----------------------------------------------------------------
      by_cases h_i'i0 : (i' : Nat) = i0
      · --------------------------------------------------------------
        -- case 2a: i' = i0
        --------------------------------------------------------------
        -- rSwap 後の i0 行は「元の rowCount 行」
        have h_eq :
          matOf R' ⟨i0, hi_i0⟩ j =
            matOf st.R ⟨st.rowCount, hi_row⟩ j := by
          -- row_right を使う
          have := matOf_rSwap_row_right
            (R := st.R)
            (i := st.rowCount) (j := i0.val)
            hi_row hi_i0 (c := j)
          simpa [R'] using this

        have : i' = ⟨i0, hi_i0⟩ := by
          apply Fin.ext
          simp [h_i'i0]
        -- 元の rowCount 行は 0 だったので、その値を引き継ぐ
        simp [this, h_eq, hz_rowCount]

      · --------------------------------------------------------------
        -- case 2b: i' はどちらの swap 行でもない
        --------------------------------------------------------------
        have hki : (i' : Nat) ≠ st.rowCount := h_i'row
        have hkj : (i' : Nat) ≠ i0 := by
          intro h
          exact h_i'i0 (by simpa using h)

        -- この場合、行 i' は rSwap でも変わらない
        have h_pres :
          matOf R' i' j = matOf st.R i' j := by
          have := matOf_rSwap_row_other
            (R := st.R)
            (i := st.rowCount) (j := i0.val) (k := i')
            hi_row hi_i0 hk hki hkj (c := j)
          simpa [R'] using this

        -- 元の R で i' 行は 0 だったので、そのまま 0
        simp [h_pres, hz_old_general]

  · ------------------------------------------------------------------
    -- I5_fac : R' = (E' : 単元行列) * M0
    ------------------------------------------------------------------
    rcases hInv.I5_fac with ⟨E, hE_unit, hE_mul⟩
    -- rSwap に対応する置換行列 P を使う
    have hi  : st.rowCount < m := h_row_lt_m
    have hj0 : i0.val     < m := i0.is_lt
    rcases matOf_rSwap_eq_P_mul (R := st.R)
        (i := st.rowCount) (j := i0.val) hi hj0 with
      ⟨P, hP_unit, hP_mul⟩

    -- mulᵣ P (matOf st.R) を左から P * (matOf st.R) とみなす
    -- （Matrix.mulᵣ の定義に応じて simp してください）
    have hP_mul' :
      matOf R' = P * matOf st.R := by
      -- mulᵣ の定義が `Matrix.mulᵣ P M = P * M` であれば simp で落ちます
      simpa [R', Matrix.mulᵣ] using hP_mul

    refine ⟨P * E, ?_, ?_⟩
    · -- P * E は単元
      exact IsUnit.mul hP_unit hE_unit
    · -- matOf R' = (P * E) * st.M0
      calc
        matOf R' = P * matOf st.R := hP_mul'
        _        = P * (E * st.M0) := by simp [hE_mul]
        _        = (P * E) * st.M0 := by
                      simp [Matrix.mul_assoc]

/- rScale で行 k を a 倍したとき、その行の成分は a 倍される -/
lemma matOf_rScale_row_scaled
  {m n K} [Field K]
  (R : Rectified m n K) {k : Nat} (hk : k < m)
  (a : K) (c : Fin n) :
  matOf (rScale R k a) ⟨k, hk⟩ c
    = a * matOf R ⟨k, hk⟩ c := by
  -- rowScale/ rScale / toMat の定義を展開して証明
  -- （rowAxpy のときと同じ系統の array-level のゴリ押し）
  have hAsize : R.A.size = m := by
    -- Rectified の定義から
    simp [R.rowSize]

  have hk': k < R.A.size := by
    simp [hAsize, hk]

  simp [rScale, hk', matOf, toMat, rowScale]

/- rScale は行 k 以外は変えない -/
lemma matOf_rScale_row_other
  {m n K} [Field K]
  (R : Rectified m n K) {k : Nat} (hk : k < m)
  (a : K) {i' : Fin m} (hne : (i' : Nat) ≠ k) (c : Fin n) :
  matOf (rScale R k a) i' c =
    matOf R i' c := by
  -- rowScale / rScale / toMat の定義と `hne` を使って
  -- 「set した index と違う indexの成分は変わらない」を証明
  have hAsize : R.A.size = m := by
    -- Rectified の定義から
    simp [R.rowSize]
  have hi'_lt_m : (i' : Nat) < m := by
    simp [i'.is_lt]
  have hk': k < R.A.size := by
    simp [hAsize, hk]
  simp [rScale, hk', matOf, toMat,
  rowScale, Array.setIfInBounds, Array.getElem_set, hne.symm]

/- rScale は「対角に a を持つ elementary scaling 行列」を左からかけたものと同じ -/
lemma matOf_rScale_eq_D_mul
  {m n K} [Field K]
  (R : Rectified m n K) {k : Nat} (hk : k < m)
  (a : K) (ha : a ≠ 0) :
  ∃ D : Matrix (Fin m) (Fin m) K,
    IsUnit D ∧
    matOf (rScale R k a) = Matrix.mulᵣ D (matOf R) := by
  -- D：対角は 1, except (k,k) = a のような行列
  -- det D = a ≠ 0 なので IsUnit D
  -- あとは「行列の k 行だけを a 倍」が mulᵣ D になることを ext で証明
  let D : Matrix (Fin m) (Fin m) K :=
    Matrix.diagonal (fun i => if (i : Nat) = k then a else 1)
  have hD_unit : IsUnit D := by
    -- det D = a なので a ≠ 0 より単元
    have h_det :
      Matrix.det D = a := by
      -- D の定義から det を計算
      simp [D]
      rw [Finset.prod_eq_single ⟨k, hk⟩]
      · simp
      · -- ケース2: i ≠ k のとき (1 になることの確認)
        intro b _ h_neq
        -- b ≠ ⟨k, hk⟩ ならば、b.val ≠ k なので if文は else 1 に落ちる
        rw [if_neg]
        intro h_eq
        apply h_neq
        apply Fin.eq_of_val_eq h_eq
      · -- ケース3: ⟨k, hk⟩ が範囲外の場合 (Fin m なのでありえない)
        simp
    have : IsUnit D.det := by
      simp [h_det, ha]
    exact (Matrix.isUnit_iff_isUnit_det D).mpr this
  -- matOf (rScale R k a) = mulᵣ D (matOf R) の証明
  refine ⟨D, hD_unit, ?_⟩
  ext i j
  -- i = k のときと i ≠ k のときで場合分け
  by_cases h_i_k : (i : Nat) = k
  · ------------------------------------------------------------------
    -- case 1: i = k → 行 k だけが a 倍される
    ------------------------------------------------------------------
    -- i を Fin k に同一視
    have hk' : k < m := hk
    have hi_eq : i = ⟨k, hk'⟩ := by
      apply Fin.ext
      simp [h_i_k]

    subst hi_eq

    -- 左辺：rScale で行 k が a 倍された
    have hL :
      matOf (rScale R k a) ⟨k, hk'⟩ j =
        a * matOf R ⟨k, hk'⟩ j := by
      -- 「スケールされた行の成分は a 倍」という rScale 用の補題
      -- （rSwap の matOf_rSwap_row_left に対応するやつ）
      -- 例えばこんな形で用意しておく：
      -- lemma matOf_rScale_row_scaled
      --   (R : Rectified m n K) {row} (hrow : row < m) (k : K) (c : Fin n) :
      --   matOf (rScale R row k) ⟨row, hrow⟩ c
      --     = k * matOf R ⟨row, hrow⟩ c
      simpa using
        matOf_rScale_row_scaled R hk' a j

    -- 右辺：対角行列 D で左から掛けると，行 k は「係数 a 倍」になる
    have hR :
      Matrix.mulᵣ D (matOf R) ⟨k, hk'⟩ j =
        a * matOf R ⟨k, hk'⟩ j := by
      -- diagonal_mul :
      -- (Matrix.diagonal v ⬝ M) i j = v i * M i j
      -- mulᵣ は単に左からの積と同じなので simp で落ちる
      simp [Matrix.mulᵣ_eq, D, Matrix.diagonal_mul]

    -- まとめて両辺を一致させる
    calc
      matOf (rScale R k a) ⟨k, hk'⟩ j
          = a * matOf R ⟨k, hk'⟩ j := hL
      _   = Matrix.mulᵣ D (matOf R) ⟨k, hk'⟩ j := hR.symm

  · ------------------------------------------------------------------
    -- case 2: i ≠ k → 行 i はそのまま
    ------------------------------------------------------------------
    have hk' : k < m := hk

    -- 左辺：行 i は rScale でも変わらない
    have hL :
      matOf (rScale R k a) i j =
        matOf R i j := by
      -- 「スケール対象以外の行はそのまま」という補題
      -- 例えば：
      -- lemma matOf_rScale_row_other
      --   (R : Rectified m n K) {row} (hrow : row < m) (k : K)
      --   {i : Fin m} (hne : (i : ℕ) ≠ row) (c : Fin n) :
      --   matOf (rScale R row k) i c
      --     = matOf R i c
      simpa using
        matOf_rScale_row_other R hk' a (hne := h_i_k) j

    -- 右辺：対角行列 D で左から掛けると，
    -- 行 i の係数は v i = if ↑i = k then a else 1 だが，
    -- 仮定 i ≠ k より 1 倍になる
    have hR :
      Matrix.mulᵣ D (matOf R) i j =
        matOf R i j := by
      have hcoeff :
        (if (i : Nat) = k then a else (1 : K)) = 1 := by
        simp [h_i_k]  -- if_neg
      -- diagonal_mul を使って，row スケールの形に落とす
      simp [Matrix.mulᵣ_eq, D, Matrix.diagonal_mul, hcoeff]

    calc
      matOf (rScale R k a) i j
          = matOf R i j := hL
      _   = Matrix.mulᵣ D (matOf R) i j := hR.symm

lemma inv_after_rScale
  {m n K} [Field K] {R : Rectified m n K} {M0 : Matrix (Fin m) (Fin n) K}
  {r0 c0 : Nat} {p0 : Fin r0 → Fin n}
  (hInv : Inv M0 R r0 c0 p0)
  {a : K} (ha : a ≠ 0) (hrow_lt_m : r0 < m) :
  Inv M0 (rScale R r0 a) r0 c0 p0 := by
  classical
  set R' := rScale R r0 a with hR'
  let hrows := hInv.I0_rows
  have hkA : r0 < R.A.size := by
    -- R.A.size = m なので
    simpa [hrows] using hrow_lt_m
  have h_bound := hInv.I1_bound

  refine
    { I0_rows := ?_
    , I0_rect := ?_
    , I1_bound := ?_
    , I1_mono  := ?_
    , I1_in    := ?_
    , I2_unit  := ?_
    , I3_left0 := ?_
    , I4_tail0 := ?_
    , I5_fac   := ?_
    }

  · ------------------------------------------------------------------
    -- I0_rows : 行数は変わらない
    ------------------------------------------------------------------
    simpa [R'] using (rScale R r0 a).rowSize

  · ------------------------------------------------------------------
    -- I0_rect : Rect 性も保たれる
    ------------------------------------------------------------------
    simpa [R'] using (rScale R r0 a).rect

  · ------------------------------------------------------------------
    -- I1_bound : r0 ≤ m, c0 ≤ n はそのまま
    ------------------------------------------------------------------
    exact hInv.I1_bound

  · ------------------------------------------------------------------
    -- I1_mono : pivot 列の StrictMono はそのまま
    ------------------------------------------------------------------
    exact hInv.I1_mono

  · ------------------------------------------------------------------
    -- I1_in : pivot 列 < c0 もそのまま
    ------------------------------------------------------------------
    exact hInv.I1_in

  · ------------------------------------------------------------------
    -- I2_unit : 既存の pivot 列は縦に単位ベクトルのまま
    ------------------------------------------------------------------
    intro i
    rcases hInv.I2_unit i with ⟨h_one_old, h_zero_old⟩

    -- pivot 行の index を Fin m に持ち上げる
    let rowOld : Fin m := Fin.castLE h_bound.1 i
    have h_rowOld_lt_r0 : (rowOld : ℕ) < r0 := by
      -- castLE の値は i.val
      simp [rowOld]  -- i.val < r0

    -- rowOld はスケールする行 r0 とは異なる
    have h_rowOld_ne_k : (rowOld : ℕ) ≠ r0 := by
      exact ne_of_lt h_rowOld_lt_r0

    -- pivot 行は rScale で変わらない
    have h_row_pres :
      ∀ j : Fin n,
        matOf R' rowOld j = matOf R rowOld j := by
      intro j
      have hk' : r0 < m := hrow_lt_m
      simpa [R'] using
        matOf_rScale_row_other (R := R) hk' a h_rowOld_ne_k j

    refine ⟨?h_one, ?h_zero⟩

    · -- pivot 成分 = 1 のまま
      have h_eq := h_row_pres (p0 i)
      have h_one_old' :
        matOf R rowOld (p0 i) = 1 := by
        simpa [rowOld] using h_one_old
      -- h_eq : matOf R' rowOld (p0 i) = matOf R rowOld (p0 i)
      -- なので 右辺を 1 に書き換える
      have : matOf R' rowOld (p0 i) = 1 := by
        simpa [h_one_old'] using h_eq
      -- 目標の行 index は定義的に rowOld
      simpa [rowOld] using this

    · -- 他の行は 0 のまま
      intro i' hi'_ne
      by_cases h_i'_k : (i' : ℕ) = r0
      · --------------------------------------------------------------
        -- case 1: i' = r0 → スケールされた行
        --------------------------------------------------------------
        have hk' : r0 < m := hrow_lt_m
        -- スケール後の pivot 列成分 = a * 元の成分
        have h_scaled :
          matOf R' ⟨r0, hk'⟩ (p0 i) =
            a * matOf R ⟨r0, hk'⟩ (p0 i) := by
          simpa [R'] using
            matOf_rScale_row_scaled (R := R) (k := r0) hk' a (p0 i)

        -- row r0 は pivot 行 rowOld とは別なので、元の R では pivot 列成分は 0
        have h_zero_old_k :
          matOf R ⟨r0, hk'⟩ (p0 i) = 0 := by
          have h_ne_rowOld :
            (⟨r0, hk'⟩ : Fin m) ≠ rowOld := by
            intro hEq
            have hv := congrArg (fun (x : Fin m) => (x : ℕ)) hEq
            have : (rowOld : ℕ) < (rowOld : ℕ) := by
              -- rowOld < r0 と hv から矛盾
              have hlt : (rowOld : ℕ) < r0 := h_rowOld_lt_r0
              -- hv : rowOld = r0
              -- これを代入すると rowOld < rowOld の形になる
              have : (r0 : ℕ) = (rowOld : ℕ) := by
                simpa using hv
              simp [this] at hlt
            exact (Nat.lt_irrefl _ this)
          -- I2_unit の「他の行は 0」
          simpa using h_zero_old ⟨r0, hk'⟩ h_ne_rowOld

        have : i' = ⟨r0, hk'⟩ := by
          apply Fin.ext
          simp [h_i'_k]

        simp [this, h_scaled, h_zero_old_k]

      · --------------------------------------------------------------
        -- case 2: i' ≠ r0 → 行そのものは変わらない
        --------------------------------------------------------------
        have hk' : r0 < m := hrow_lt_m
        have h_pres :
          matOf R' i' (p0 i) =
            matOf R i' (p0 i) := by
          simpa [R'] using
            matOf_rScale_row_other (R := R) hk' a h_i'_k (p0 i)

        -- 元の R では「pivot 行以外」は 0
        have h_zero_old' :
          matOf R i' (p0 i) = 0 :=
          h_zero_old i' hi'_ne

        simp [h_pres, h_zero_old']

  · ------------------------------------------------------------------
    -- I3_left0 : pivot 行の左側は 0 のまま
    ------------------------------------------------------------------
    intro i j hj_lt
    -- pivot 行
    let rowOld : Fin m := Fin.castLE h_bound.1 i
    have h_rowOld_lt_r0 : (rowOld : ℕ) < r0 := by
      simp [rowOld]
    have h_rowOld_ne_k : (rowOld : ℕ) ≠ r0 := by
      exact ne_of_lt h_rowOld_lt_r0

    -- 元の R で左側 0
    have hz_old :
      matOf R rowOld j = 0 := by
      have := hInv.I3_left0 i j hj_lt
      simpa [rowOld] using this

    -- rScale で pivot 行は変わらない
    have hk' : r0 < m := hrow_lt_m
    have h_row_pres :
      matOf R' rowOld j = matOf R rowOld j := by
      simpa [R'] using
        matOf_rScale_row_other (R := R) hk' a h_rowOld_ne_k j

    -- castLE 版と rowOld は defeq
    calc
      matOf R' (Fin.castLE h_bound.1 i) j
          = matOf R' rowOld j := by rfl
      _   = matOf R rowOld j := h_row_pres
      _   = 0 := hz_old

  · ------------------------------------------------------------------
    -- I4_tail0 : まだ pivot でない列 j < c0 では、行 r0 以降は 0 のまま
    ------------------------------------------------------------------
    intro j hj_lt h_noPivot i' hi_ge
    have hk' : r0 < m := hrow_lt_m

    -- 元の R では tail 部分は全部 0
    have hz_old_general :
      matOf R i' j = 0 :=
      hInv.I4_tail0 j hj_lt h_noPivot i' hi_ge

    by_cases h_i'_k : (i' : ℕ) = r0
    · --------------------------------------------------------------
      -- case 1: i' = r0 → スケールされた行
      --------------------------------------------------------------
      -- R での r0 行の j 成分も 0
      have hz_old_k :
        matOf R ⟨r0, hk'⟩ j = 0 := by
        -- hi_ge : r0 ≤ (⟨r0, hk'⟩ : Fin m).val は refl
        have hi_ge' : (r0 : ℕ) ≤ (⟨r0, hk'⟩ : Fin m) := by
          simp
        simpa using
          hInv.I4_tail0 j hj_lt h_noPivot ⟨r0, hk'⟩ hi_ge'

      -- スケールされた行の j 成分 = a * 0
      have h_scaled :
        matOf R' ⟨r0, hk'⟩ j =
          a * matOf R ⟨r0, hk'⟩ j := by
        simpa [R'] using
          matOf_rScale_row_scaled (R := R) (k := r0) hk' a j
      have : i' = ⟨r0, hk'⟩ := by
        apply Fin.ext
        simp [h_i'_k]
      simp [this, h_scaled, hz_old_k]

    · --------------------------------------------------------------
      -- case 2: i' ≠ r0 → 行はそのまま
      --------------------------------------------------------------
      have h_pres :
        matOf R' i' j = matOf R i' j := by
        simpa [R'] using
          matOf_rScale_row_other (R := R) hk' a h_i'_k j

      simp [h_pres, hz_old_general]

  · ------------------------------------------------------------------
    -- I5_fac : factorization を更新（スケーリング行列を掛けたとみなす）
    ------------------------------------------------------------------
    rcases hInv.I5_fac with ⟨E, hE_unit, hE_mul⟩
    -- rScale に対応する対角行列 D
    rcases matOf_rScale_eq_D_mul R hrow_lt_m a ha with
      ⟨D, hD_unit, hD_mul⟩

    -- mulᵣ D (matOf R) = D * matOf R （mulᵣ_eq を使う）
    have hD_mul' :
      matOf R' = D * matOf R := by
      simpa [R', Matrix.mulᵣ_eq] using hD_mul

    refine ⟨D * E, ?_, ?_⟩
    · -- 単元の積は単元
      exact IsUnit.mul hD_unit hE_unit
    · -- matOf R' = (D * E) * M0
      calc
        matOf R'
            = D * matOf R := hD_mul'
        _   = D * (E * M0) := by simp [hE_mul]
        _   = (D * E) * M0 := by
                  simp [Matrix.mul_assoc]

lemma extendPivot_strictMono_state
  {m n K} [Field K] {st : GEStateP m n K}
  (hcol : st.colPtr < n) :
  StrictMono (extendPivot st.pivot ⟨st.colPtr, hcol⟩) := by
  -- st.inv から元々の StrictMono と「全部 colPtr 未満」を取り出す
  have hp  : StrictMono st.pivot := st.inv.I1_mono
  have hc  : ∀ i, st.pivot i < ⟨st.colPtr, hcol⟩ := by
    intro i
    -- I1_in : ∀ i, p0 i < c0
    -- ここで c0 = st.colPtr なので値レベルで < st.colPtr
    have h := st.inv.I1_in i
    -- Fin n 上に持ち上げるだけ
    simpa using h
  exact extendPivot_strictMono hp hc

lemma extendPivot_in
  {m n K} [Field K] {st : GEStateP m n K}
  (hcol : st.colPtr < n) :
  ∀ i, extendPivot st.pivot ⟨st.colPtr, hcol⟩ i < st.colPtr + 1 := by
  -- i < rowCount の場合はもとの pivot < colPtr
  -- 新しいインデックス rowCount では colPtr < colPtr + 1
  intro i
  by_cases h_i_rowCount : i = ⟨st.rowCount, by simp⟩
  · ----------------------------------------------------------------
    -- case 1: i = rowCount
    ----------------------------------------------------------------
    have : extendPivot st.pivot ⟨st.colPtr, hcol⟩ i
          = ⟨st.colPtr, hcol⟩ := by
      simp [h_i_rowCount]
      unfold extendPivot
      simp
    conv =>
      lhs
      rw [this]
      simp
    simp
  · ----------------------------------------------------------------
    -- case 2: i ≠ rowCount
    ----------------------------------------------------------------
    unfold extendPivot
    have h_i_lt : (i : ℕ) < st.rowCount := by
      -- i ≠ rowCount なので i.val < rowCount
      apply Nat.lt_of_le_of_ne
      · -- i ≤ st.rowCount の証明
        exact Nat.le_of_lt_succ i.is_lt
      · -- i.val ≠ rowCount の証明
        intro h_eq
        exact h_i_rowCount (by
          apply Fin.ext
          simp [h_eq]
        )
    simp [h_i_lt]
    have : (st.pivot ⟨i.val, h_i_lt⟩).val < (⟨st.colPtr, hcol⟩ : Fin n).val := by
      -- st.inv.I1_in を使う
      have h := st.inv.I1_in ⟨i.val, h_i_lt⟩
      simpa using h
    exact Nat.lt_succ_of_lt this


lemma newPivotRow_left_zero
  {m n K} [Field K]
  {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (hsome : findPivot_spec st hcol = some i0)
  -- R₂ は rSwap + rScale などを施した後の状態
  (R₂ : Rectified m n K)
  (hInv_R₂ : Inv st.M0 R₂ st.rowCount st.colPtr st.pivot) :
  ∀ j : Fin n, (j : ℕ) < st.colPtr →
    (matOf R₂) ⟨st.rowCount, (by
      -- rowCount < m を示す
      have h_pivot :=
        findPivot_spec_some_sound (st := st) (hcol := hcol) hsome
      rcases h_pivot with ⟨h_row_le_i0, _h_nz⟩
      have h_row_lt_m : st.rowCount < m :=
        lt_of_le_of_lt h_row_le_i0 i0.is_lt
      exact h_row_lt_m
    )⟩ j = 0 := by
  -- pivot 情報から rowCount < m を手に入れておく
  have h_pivot :=
    findPivot_spec_some_sound (st := st) (hcol := hcol) hsome
  rcases h_pivot with ⟨h_row_le_i0, _h_nz⟩
  have h_row_lt_m : st.rowCount < m :=
    lt_of_le_of_lt h_row_le_i0 i0.is_lt

  -- rowCount 行を Fin m にしたもの
  let rowFin : Fin m := ⟨st.rowCount, h_row_lt_m⟩
  -- 証明したいのは「rowFin 行の j 列が 0」
  intro j hj_lt
  -- 列 j がこれまでの pivot 列かどうかで場合分け
  by_cases h_exists : ∃ i : Fin st.rowCount, st.pivot i = j
  · ----------------------------------------------------------------
    -- ケース 1: j は既存の pivot 列
    ----------------------------------------------------------------
    rcases h_exists with ⟨i, hi⟩

    have h_unit := hInv_R₂.I2_unit i
    rcases h_unit with ⟨_h_one, h_zero_col⟩

    -- pivot 行の index は Fin.castLE ... i（値は i）
    -- rowFin の値は st.rowCount
    have hi_lt_row : (i : ℕ) < st.rowCount := i.is_lt
    have h_ne : rowFin ≠ Fin.castLE hInv_R₂.I1_bound.1 i := by
      -- 値が違うので ≠
      -- castLE しても値は i のまま
      -- rowFin.val = rowCount > i.val
      have : (Fin.castLE hInv_R₂.I1_bound.1 i : Fin m).val = i.val := rfl
      -- よって castLE i < rowFin
      unfold rowFin
      have hi_neq_row : st.rowCount ≠ i.val := by
        exact Nat.ne_of_gt hi_lt_row
      apply Fin.val_ne_iff.1
      simp [hi_neq_row]

    -- I2_unit の「pivot 行以外は 0」を rowFin に適用
    have h_zero_at_pivot :
      matOf R₂ rowFin (st.pivot i) = 0 :=
      h_zero_col rowFin h_ne

    -- しかし j = st.pivot i なので、そのままゴール
    simpa [rowFin, hi] using h_zero_at_pivot

  · ----------------------------------------------------------------
    -- ケース 2: j はどの pivot 列とも一致しない
    ----------------------------------------------------------------
    -- h_exists が偽 ⇒ 全 i について st.pivot i ≠ j
    have h_ne_pivot :
      ∀ i : Fin st.rowCount, st.pivot i ≠ j := by
      intro i hi_eq
      exact h_exists ⟨i, hi_eq⟩ |> False.elim

    -- Inv の I4_tail0 を使う：
    -- I4_tail0 :
    --   ∀ j : Fin n, (j : Nat) < c0 →
    --     (∀ i : Fin r0, p0 i ≠ j) →
    --     ∀ i' : Fin m, (r0 : Nat) ≤ (i' : Nat) →
    --       matOf R0 i' j = 0
    have h_tail :=
      hInv_R₂.I4_tail0 j hj_lt h_ne_pivot rowFin (by
        -- rowCount ≤ rowFin.val = rowCount
        exact le_rfl)

    -- これがちょうどゴール
    simpa [rowFin] using h_tail


/- rAxpy は pivot 行そのものは変えない -/
lemma matOf_rAxpy_pivot_row
  {m n K} [Field K]
  (R : Rectified m n K) (i row : Nat) (a : K)
  (hi : i < m)
  (hrow : row < m)
  (hne : i ≠ row) :
  ∀ col' : Fin n,
    matOf (rAxpy R i row a) ⟨row, hrow⟩ col' =
      matOf R ⟨row, hrow⟩ col' := by
  intro col'
  unfold rAxpy
  -- A.size = m を作る
  have hsize : R.A.size = m := R.rowSize
  have hiA   : i   < R.A.size := by simpa [hsize] using hi
  have hrowA : row < R.A.size := by simpa [hsize] using hrow
  have hik : i < R.A.size ∧ row < R.A.size := ⟨hiA, hrowA⟩

  -- `rAxpy` の分岐は hik の `if_pos` ブランチに入る
  simp [hik, matOf, rowAxpy]  -- `rowAxpy` と `toMat` が展開される

  -- ここで underlying array は `R.A.set! i newRow`
  -- 我々は `row` 行を見ているが，set! は行 `i` だけを書き換える
  have hrowNe : (row : Nat) ≠ i := by
    exact ne_comm.mp hne

  simp [Array.setIfInBounds, hiA,
  toMat, Array.getElem_set, hrowNe.symm]

/- `rAxpy R dst src a` は src 行を変えない -/
lemma rAxpy_src_row_unchanged
  {m n K} [Field K]
  (R : Rectified m n K)
  {src dst : Nat} (hsrc : src < R.A.size) (hdst : dst < R.A.size)
  (hne : dst ≠ src) (a : K) :
  (rAxpy R dst src a).A[src]'(by
    have hsize :=
      preserve_rowSize_rowAxpy
      R.A R.rowSize dst src a
      (
        by
          have hsize : R.A.size = m := R.rowSize
          simpa [hsize] using hdst
      )
      (
        by
          have hsize : R.A.size = m := R.rowSize
          simpa [hsize] using hsrc
      ) R.rect
    have : (rAxpy R dst src a).A.size = (rowAxpy dst src a R.A n R.rect).size := by
      simp [rAxpy, hsrc, hdst]
    have : src < (rAxpy R dst src a).A.size := by
      rw [this, hsize]
      conv => rhs; rw [R.rowSize.symm]
      exact hsrc
    exact this
  ) = R.A[src] := by
  -- rAxpy の実装が「dst 行だけ書き換える」ので，
  -- `dst = src` の場合だけ注意して、そのケースを排除するか
  -- 定義を展開して `if` をさばいていく感じ。
  --
  -- ここはあなたの rAxpy の定義に合わせて
  --   simp [rAxpy, Array.set!, hdst, hsrc, ...]
  -- でゴリゴリ書けるはず。
  unfold rAxpy
  simp [hdst, hsrc, rowAxpy, Array.setIfInBounds, Array.getElem_set]
  intro h_eq
  exact False.elim (hne h_eq)

lemma rAxpy_other_row_unchanged
  {m n K} [Field K]
  (R : Rectified m n K)
  {src dst j : Nat} (hsrc : src < R.A.size) (hdst : dst < R.A.size)
  (hj : j < R.A.size) (hjne : j ≠ dst) (a : K) :
  (rAxpy R dst src a).A[j]'(
    by
      have hsize :=
        preserve_rowSize_rowAxpy
        R.A R.rowSize dst src a
        (
          by
            have hsize : R.A.size = m := R.rowSize
            simpa [hsize] using hdst
        )
        (
          by
            have hsize : R.A.size = m := R.rowSize
            simp [hsize] at hsrc
            exact hsrc
        ) R.rect
      have : (rAxpy R dst src a).A.size = (rowAxpy dst src a R.A n R.rect).size := by
        simp [rAxpy, hsrc, hdst]
      have : j < (rAxpy R dst src a).A.size := by
        rw [this, hsize]
        conv => rhs; rw [R.rowSize.symm]
        exact hj
      exact this
  ) = R.A[j]'hj:= by
  unfold rAxpy
  simp [hdst, hsrc, rowAxpy, Array.setIfInBounds, Array.getElem_set, hjne.symm]

/- TODO: matOf, toMat を展開して中身が等しいことを示せた稀有な例 -/
/- pivot 行の `col'` 成分が 0 なら、rAxpy は `col'` 列全体を変えない -/
lemma matOf_rAxpy_preserve_col
  {m n K} [Field K]
  (R : Rectified m n K) (i row : Nat) (α : K)
  (hi : i < m) (hrow : row < m)
  (col' : Fin n)
  (h_pivot_zero :
    matOf R ⟨row, by
      have hsize : R.A.size = m := R.rowSize
      simpa [hsize] using hrow⟩ col' = 0) :
  ∀ i' : Fin m,
    matOf (rAxpy R i row α) i' col' =
      matOf R i' col' := by
  intro i'
  -- Array 側のインデックスに変換
  have hsize : R.A.size = m := R.rowSize
  have hiA   : i   < R.A.size := by simpa [hsize] using hi
  have hrowA : row < R.A.size := by simpa [hsize] using hrow

  by_cases h_eq : (i' : Nat) = i
  · subst h_eq

    unfold rAxpy
    -- rAxpy の if を落とすために hik を作る
    have hik : i' < R.A.size ∧ row < R.A.size := ⟨hiA, hrowA⟩

    simp [hik, matOf, rowAxpy, Array.setIfInBounds, toMat]  -- ← LHS が

    -- pivot 行の col' が 0 であること
    have h_row_zero : matOf R ⟨row, hrow⟩ col' = 0 := by
      simpa using h_pivot_zero

    -- あとは α * 0 = 0 を消せばよい
    simp [matOf, toMat] at h_row_zero
    exact Or.inr h_row_zero

  · ----------------------------------------------------------------
    -- ■ ケース2: i' ≠ i（触っていない行）
    ----------------------------------------------------------------
    unfold rAxpy
    simp [hiA, hrowA, matOf, rowAxpy,
    Array.setIfInBounds, toMat, Array.getElem_set]
    have : i ≠ (i' : Nat) := by
      exact ne_comm.mp h_eq
    simp [this]


/- 元の pivot 行が 0 なら掃き出し loop 後も要素は変わらない -/
lemma clearPivotCol_loop_preserve_col
  {m n K} [Field K]
  (row col : Nat) (hcol : col < n)
  (col' : Fin n) :
  ∀ (R : Rectified m n K) (hrow : row < m),
    (matOf R ⟨row, by
        have hsize : R.A.size = m := R.rowSize
        simpa [hsize] using hrow⟩ col' = 0) →
    ∀ (i : Nat) (i' : Fin m),
      matOf (clearPivotCol_loop R row col hcol i) i' col' =
        matOf R i' col' := by
  intro R hrow h_pivot_zero

  ----------------------------------------------------------------
  -- 強い帰納法の本体：R も仮定に含めた形に強化する
  ----------------------------------------------------------------
  have main :
    ∀ (R₀ : Rectified m n K) (hrow₀ : row < m)
      (h_piv₀ :
        matOf R₀ ⟨row, by
          have hsize : R₀.A.size = m := R₀.rowSize
          simpa [hsize] using hrow₀⟩ col' = 0)
      (k i : Nat), i + k = m →
      ∀ i' : Fin m,
        matOf (clearPivotCol_loop R₀ row col hcol i) i' col' =
          matOf R₀ i' col' := by

    intro R₀ hrow₀ h_piv₀ k
    induction k generalizing R₀ hrow₀ h_piv₀ with

    ------------------------------------------------------------
    -- k = 0 の場合：i + 0 = m なので i = m、ループは終了して R₀ が返る
    ------------------------------------------------------------
    | zero =>
      intro i hi i'
      have hi_eq : i = m := by
        simpa using hi
      subst hi_eq
      -- i = m なら clearPivotCol_loop R₀ ... m = R₀
      simp [clearPivotCol_loop]

    ------------------------------------------------------------
    -- k.succ の場合：i + (k+1) = m を仮定
    ------------------------------------------------------------
    | succ k hk =>
      intro i hi i'
      -- i + (k+1) = m から i < m を得る
      have hi_lt_m : i < m := by
        have : i < i + (Nat.succ k) :=
          Nat.lt_add_of_pos_right (Nat.succ_pos k)
        simpa [hi] using this

      -- (i+1) + k = m も計算しておく（再帰呼び出し用）
      have hi_next : i.succ + k = m := by
        -- i.succ = i + 1 を使って書き換え
        have := hi
        simpa [Nat.succ_eq_add_one, Nat.add_comm,
              Nat.add_left_comm, Nat.add_assoc] using this

      -- R₀.A.size = m, row < R₀.A.size, i < R₀.A.size を作る
      have hsize₀ : R₀.A.size = m := R₀.rowSize
      have hrowA₀ : row < R₀.A.size := by
        simpa [hsize₀] using hrow₀
      have hiA : i < R₀.A.size := by
        simpa [hsize₀] using hi_lt_m

      -- 1ステップ clearPivotCol_loop を展開
      unfold clearPivotCol_loop
      have hi' : i < m := hi_lt_m
      simp [hi']  -- `if hi : i < m` の `then` 側に入る

      -- ここで i = row / i ≠ row を場合分け
      by_cases hrowi : i = row

      ----------------------------------------------------------
      -- (1) pivot 行のとき：何もせず i+1 から再スタート
      ----------------------------------------------------------
      · subst hrowi
        simp
        -- (i+1) + k = m なので IH を R₀ に対して適用
        have : (i + 1) + k = m := by
          simpa [Nat.succ_eq_add_one, Nat.add_comm,
                Nat.add_left_comm, Nat.add_assoc] using hi_next

        simpa [Nat.succ_eq_add_one] using
          hk (R₀ := R₀) (hrow₀ := hrow₀) (h_piv₀ := h_piv₀)
            (i := i + 1) this i'

      ----------------------------------------------------------
      -- (2) 非 pivot 行：rAxpy してから i+1 へ
      ----------------------------------------------------------
      · -- i ≠ row: rAxpy してから i+1 へ
        have hiA : i < R₀.A.size := by
          simpa [hsize₀] using hi_lt_m
        let fi : Fin m := ⟨i, hi_lt_m⟩
        let a  : K := matOf R₀ fi ⟨col, hcol⟩
        let R' : Rectified m n K := rAxpy R₀ i row (-a)

        -- (2-2) まず「列 col' は R₀ と R' で同じ」という補題を使う
        have h_col_pres :
          ∀ j' : Fin m,
            matOf R' j' col' = matOf R₀ j' col' := by
          intro j'
          have hi_m   : i   < m := hi_lt_m
          have hrow_m : row < m := hrow₀
          simpa [R', a] using
            matOf_rAxpy_preserve_col R₀ i row (-a)
              hi_m hrow_m col' h_piv₀ j'

        -- (2-1) pivot 行 col' が 0 のままであることは、h_col_pres から引き出せる
        have h_piv_R' :
          matOf R' ⟨row, by
              have hsize' : R'.A.size = m := R'.rowSize
              simpa [hsize'] using hrow₀⟩ col' = 0 := by
          -- pivot 行のインデックスで h_col_pres を評価
          have h_piv₀' : matOf R₀ ⟨row, hrow₀⟩ col' = 0 := by
            -- ここは `matOf` の定義次第だけど、多くの場合は証明部が違うだけなので
            -- そのまま `simpa` で落ちる
            simpa using h_piv₀
          have := h_col_pres ⟨row, hrow₀⟩
          -- this : matOf R' ⟨row, hrow₀⟩ col' = matOf R₀ ⟨row, hrow₀⟩ col'
          simpa [h_piv₀'] using this

        -- (2-3) strong IH を R' に対して適用
        have h_ind :
          matOf (clearPivotCol_loop R' row col hcol (i+1)) i' col' =
            matOf R' i' col' :=
          hk (R₀ := R') (hrow₀ := hrow₀) (h_piv₀ := h_piv_R')
            (i := i + 1) hi_next i'

        -- 右辺の R' を R₀ に戻す：h_col_pres を使う
        have h_col_pres_i' : matOf R' i' col' = matOf R₀ i' col' :=
          h_col_pres i'
        -- 左辺は既にゴールの左辺そのものなので、右だけ差し替えれば終わり
        have := h_ind.trans h_col_pres_i'
        -- ここで `simp` を軽くかけて終わり
        simp [R', a, fi] at this
        simp [hrowi, this]

  ----------------------------------------------------------------
  -- main を使って元のステートメントを証明
  ----------------------------------------------------------------
  intro i i'
  by_cases hi : i < m
  · -- i < m の場合は k := m - i で strong recursion を使う
    have hi_eq : i + (m - i) = m := Nat.add_sub_of_le (Nat.le_of_lt hi)
    exact main R hrow h_pivot_zero (m - i) i hi_eq i'
  · -- i ≥ m の場合はループは即座に終了し，常に R が返る
    have hnot : ¬ i < m := hi
    simp [clearPivotCol_loop, hnot]


lemma clearPivotCol_preserve_col
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat)
  (hcol : col < n) (hrow : row < m)
  (col' : Fin n)
  (h_pivot_zero : matOf R ⟨row, by
      -- row < R.A.size を作る
      have hsize : R.A.size = m := R.rowSize
      simpa [hsize] using hrow⟩ col' = 0) :
  ∀ i' : Fin m,
    matOf (clearPivotCol R row col hcol) i' col' =
      matOf R i' col' := by
  intro i'
  -- clearPivotCol の定義を展開して、`i = 0` を使うだけ
  have h := clearPivotCol_loop_preserve_col
    (row := row) (col := col) (hcol := hcol) (col' := col')
    (R := R) (hrow := hrow) h_pivot_zero
  -- h : ∀ i i', matOf (clearPivotCol_loop R row col hcol i) i' col' = matOf R i' col'
  -- なので i = 0 を代入
  have h0 := h 0 i'
  simpa [clearPivotCol] using h0


/- pivot 行 `row` を使って列 `col` を掃き出すループは，
    何ステップ進めても pivot 行 `row` の行ベクトルを変えない（Array 版） -/
lemma clearPivotCol_loop_row_unchanged_simple
  {m n K} [Field K]
  {row col : Nat}
  (hrow : row < m) (hcol : col < n) :
  ∀ (R : Rectified m n K) (i : Nat) (hiA : i ≤ m),
    (clearPivotCol_loop R row col hcol i).A[row]'(
      by
        have hsize :=
          preserve_rowSize_clearPivotCol_loop
            row col hcol i R
        have : row < (clearPivotCol_loop R row col hcol i).A.size := by
          rw [hsize]
          simp [hrow]
          exact hiA
        exact this
    ) = R.A[row]'(
      by
        have hsize : R.A.size = m := R.rowSize
        simpa [hsize] using hrow
    ) := by
  -- k := m - i を measure に取って強い帰納法
  have main :
    ∀ (k i : Nat) (R : Rectified m n K) (hmi : i + k = m),
      m - i = k →
      (clearPivotCol_loop R row col hcol i).A[row]'(
        by
          have hsize :=
            preserve_rowSize_clearPivotCol_loop
              row col hcol i R
          have : row < (clearPivotCol_loop R row col hcol i).A.size := by
            rw [hsize]
            simp [hrow]
            exact Nat.le.intro hmi
          exact this
      ) = R.A[row]'(
        by
          have hsize : R.A.size = m := R.rowSize
          simpa [hsize] using hrow
      ) := by
    intro k
    induction k with
    | zero =>
      intro i R hmi hmi_eq
      -- m - i = 0 ⇒ i ≥ m
      have hi_ge : m ≤ i := Nat.le_of_sub_eq_zero (by simp [hmi_eq])
      have hi_lt : ¬ i < m := not_lt_of_ge hi_ge
      -- i ≥ m のとき clearPivotCol_loop は R を返す
      have hloop : clearPivotCol_loop R row col hcol i = R := by
        simp [clearPivotCol_loop, hi_lt]
      simp [hloop]
    | succ k ih =>
      intro i R hmi hmi_eq
      -- m - i = k.succ ⇒ i < m
      have hi_lt : i < m := by
        by_contra hge
        have hge' : m ≤ i := Nat.le_of_not_gt hge
        have hzero : m - i = 0 := Nat.sub_eq_zero_of_le hge'
        have : (0 : Nat) = Nat.succ k := by simp [hzero] at hmi_eq
        exact Nat.succ_ne_zero k this.symm

      -- m - (i+1) = k
      have hmi_succ : m - (i+1) = k := by
        -- `Nat.sub_succ` を使うか，`simp` で落とす
        have := congrArg Nat.pred hmi_eq
        -- 実装は環境に合わせて調整してね
        -- だいたい `simp [Nat.sub, hi_lt]` で通るはず
        simp at this
        exact this
      -- `i = row` かどうかで場合分け
      by_cases hrow_eq : i = row
      · -- pivot 行のインデックスのときは何もしないで i+1 に進む branch
        have : i + 1 + k = m := by
          -- i + 1 + k = (i + k) + 1 = m
          rw [Nat.add_assoc, Nat.add_comm 1 k, hmi]
        have hIH := ih (i+1) R this hmi_succ
        -- `clearPivotCol_loop` の定義から
        --   clearPivotCol_loop R … i = clearPivotCol_loop R … (i+1)
        have hloop :
          clearPivotCol_loop R row col hcol i =
          clearPivotCol_loop R row col hcol (i+1) := by
          have hiA : i ≤ m := Nat.le.intro hmi
          -- i < m なので `if hi : i < m` で true
          conv =>
            lhs
            unfold clearPivotCol_loop
            simp [hi_lt, hrow_eq]
          have : row < m := by
            rw [hrow_eq] at hi_lt
            exact hi_lt
          simp [this, hrow_eq]

        -- 行 row に関しても同じ
        have hloop_row :
          (clearPivotCol_loop R row col hcol i).A[row]'(
            by
              have hsize :=
                preserve_rowSize_clearPivotCol_loop
                  row col hcol i R
              have : row < (clearPivotCol_loop R row col hcol i).A.size := by
                rw [hsize]
                simp [hrow]
                exact Nat.le.intro hmi
              exact this
          ) =
          (clearPivotCol_loop R row col hcol (i+1)).A[row]'(
            by
              have hsize :=
                preserve_rowSize_clearPivotCol_loop
                  row col hcol (i+1) R
              have : row < (clearPivotCol_loop R row col hcol (i+1)).A.size := by
                rw [hsize]
                simp [hrow]
                exact Nat.le.intro (by
                  have : i + 1 + k = m := by
                    rw [Nat.add_assoc, Nat.add_comm 1 k, hmi]
                  exact this)
              exact this
          ) := by
          simp [hloop]

        -- これでゴールに到達
        --   (loop i).A[row] = (loop (i+1)).A[row] = R.A[row]
        -- の形
        -- `' の index 証明付き版も `simp` でだいたいそのまま落ちる
        -- （型が微妙に合わないなら `have` で配列等式→成分等式に落とす）
        -- ここは `simp` ではなく `calc` で書くと分かりやすい：
        -- （↓型の細かい所は環境に応じて微調整してね）
        have hcore :
          (clearPivotCol_loop R row col hcol i).A[row]'(
            by
              have hsize :=
                preserve_rowSize_clearPivotCol_loop
                  row col hcol i R
              have : row < (clearPivotCol_loop R row col hcol i).A.size := by
                rw [hsize]
                simp [hrow]
                exact Nat.le.intro hmi
              exact this
          ) = R.A[row]'(
            by
              have hsize : R.A.size = m := R.rowSize
              simpa [hsize] using hrow
          ) := by
          calc
            (clearPivotCol_loop R row col hcol i).A[row]'(
              by
                have hsize :=
                  preserve_rowSize_clearPivotCol_loop
                    row col hcol i R
                have : row < (clearPivotCol_loop R row col hcol i).A.size := by
                  rw [hsize]
                  simp [hrow]
                  exact Nat.le.intro hmi
                exact this
            )
                = (clearPivotCol_loop R row col hcol (i+1)).A[row]'(
                      by
                        have hsize :=
                          preserve_rowSize_clearPivotCol_loop
                            row col hcol (i+1) R
                        have : row < (clearPivotCol_loop R row col hcol (i+1)).A.size := by
                          rw [hsize]
                          simp [hrow]
                          exact Nat.le.intro (by
                            have : i + 1 + k = m := by
                              rw [Nat.add_assoc, Nat.add_comm 1 k, hmi]
                            exact this)
                        exact this
                    ) := hloop_row
            _   = R.A[row]'(
                      by
                        have hsize : R.A.size = m := R.rowSize
                        simpa [hsize] using hrow
                  ) := hIH
        exact hcore
      · -- i ≠ row のとき：一度 rAxpy してから i+1 へ
        have hi_lt' : i < m := hi_lt
        -- fi, a, R' を定義（clearPivotCol_loop の定義と揃える）
        let fi : Fin m :=
          ⟨i, by simpa [R.rowSize] using hi_lt'⟩
        let a : K := (matOf R) fi ⟨col, hcol⟩
        let R' : Rectified m n K := rAxpy R i row (-a)
        have hmi' : i + 1 + k = m := by
          -- i + 1 + k = (i + k) + 1 = m
          rw [Nat.add_assoc, Nat.add_comm 1 k, hmi]
        -- IH を R', i+1 に適用
        have hIH := ih (i+1) R' hmi' hmi_succ

        -- rAxpy は src 行 row を変えない
        have hsizeA : R.A.size = m := by simpa using R.rowSize
        have hsrc : row < R.A.size := by
          simpa [hsizeA] using hrow
        have hdst : i < R.A.size := by
          simpa [hsizeA] using hi_lt'
        have hRow_un :
          R'.A[row]'(
            by
              have hsize' := preserve_rowSize_rowAxpy
                R.A R.rowSize i row (-a)
                (by simpa [hsizeA] using hdst)
                (by simpa [hsizeA] using hsrc) R.rect
              have : R'.A.size = (rowAxpy i row (-a) R.A n R.rect).size := by
                unfold R'
                simp [rAxpy, hdst, hsrc]
              have : row < R'.A.size := by
                rw [this, hsize']
                simp [hrow]
              exact this
            ) = R.A[row] := by
          -- ここで既存の `rAxpy_src_row_unchanged` を使う想定。
          -- 実際はインデックス証明を合わせるために
          -- `simp [R', rowAxpy, fi, a]` で調整。
          simpa [R', fi, a] using
            rAxpy_src_row_unchanged R hsrc hdst hrow_eq (-a)

        -- 1ステップ分のループの展開
        have hloop :
          (clearPivotCol_loop R row col hcol i).A[row]'(
            by
              have hsize :=
                preserve_rowSize_clearPivotCol_loop
                  row col hcol i R
              have : row < (clearPivotCol_loop R row col hcol i).A.size := by
                rw [hsize]
                simp [hrow]
                exact Nat.le.intro hmi
              exact this
          ) =
            (clearPivotCol_loop R' row col hcol (i+1)).A[row]'(
              by
                have hsize :=
                  preserve_rowSize_clearPivotCol_loop
                    row col hcol (i+1) R'
                have : row < (clearPivotCol_loop R' row col hcol (i+1)).A.size := by
                  rw [hsize]
                  simp [hrow]
                  exact Nat.le.intro hmi'
                exact this
            ) := by
          conv =>
            lhs
            unfold clearPivotCol_loop
            simp [hi_lt', hrow_eq]

        calc
          (clearPivotCol_loop R row col hcol i).A[row]'(
            by
              have hsize :=
                preserve_rowSize_clearPivotCol_loop
                  row col hcol i R
              have : row < (clearPivotCol_loop R row col hcol i).A.size := by
                rw [hsize]
                simp [hrow]
                exact Nat.le.intro hmi
              exact this
          )
              = (clearPivotCol_loop R' row col hcol (i+1)).A[row]'(
                by
                  have hsize :=
                    preserve_rowSize_clearPivotCol_loop
                      row col hcol (i+1) R'
                  have : row < (clearPivotCol_loop R' row col hcol (i+1)).A.size := by
                    rw [hsize]
                    simp [hrow]
                    exact Nat.le.intro hmi'
                  exact this
              ) := hloop
          _   = R'.A[row]'(
                by
                  have hsize' := preserve_rowSize_clearPivotCol_loop
                    row col hcol (i+1) R'
                  have : row < (clearPivotCol_loop R' row col hcol (i+1)).A.size := by
                    rw [hsize']
                    simp [hrow]
                    exact Nat.le.intro hmi'
                  have hmi_le : (i + 1) ≤ m := by
                    have : i + 1 + k = m := by
                      rw [Nat.add_assoc, Nat.add_comm 1 k, hmi]
                    exact Nat.le.intro this
                  have hsize'' := hsize' hmi_le
                  simp [hsize'', R'.rowSize.symm] at this
                  exact this
          ) := hIH
          _   = R.A[row] := hRow_un

  -- 本体：k := m - i で main を起動
  intro R i hiA
  have : i + (m - i) = m := Nat.add_sub_of_le hiA
  exact main (m - i) i R this rfl

/- clearPivotCol_loop の全ステップで pivot 行 `row` は不変 -/
/- clearPivotCol_loop の全ステップで pivot 行 `row` は不変（Fin / `' 付き版） -/
lemma clearPivotCol_loop_row_unchanged
  {m n K} [Field K]
  {row col : Nat}
  (hrow : row < m) (hcol : col < n) :
  ∀ (R : Rectified m n K) (i : Nat) (hiA : i ≤ m),
    (clearPivotCol_loop R row col hcol i).A[row]'(by
      -- row < (clearPivotCol_loop … i).A.size の証明
      have hsize :=
        preserve_rowSize_clearPivotCol_loop
          (row := row) (col := col) (hcol := hcol)
          (i := i) (R := R) hiA
      have hr : row < m := hrow
      -- hsize : size = m なので書き換え
      simpa [hsize] using hr
    )
    =
    R.A[row]'(by
      -- row < R.A.size の証明
      have hsize : R.A.size = m := by simpa using R.rowSize
      have hr : row < m := hrow
      have : row < R.A.size := by simpa [hsize] using hr
      exact this
    ) := by
  classical
  intro R i hiA
  -- simple 版で行ベクトルの等式をもらう
  have hArr :
    (clearPivotCol_loop R row col hcol i).A[row]'(
      by
        -- row < (clearPivotCol_loop … i).A.size の証明
        have hsize :=
          preserve_rowSize_clearPivotCol_loop
            (row := row) (col := col) (hcol := hcol)
            (i := i) (R := R) hiA
        have hr : row < m := hrow
        -- hsize : size = m なので書き換え
        simpa [hsize] using hr
    ) = R.A[row]'(
      by
        have hsize : R.A.size = m := by simpa using R.rowSize
        have hr : row < m := hrow
        have : row < R.A.size := by simpa [hsize] using hr
        exact this
    ) :=
    clearPivotCol_loop_row_unchanged_simple
      (m := m) (n := n) (row := row) (col := col)
      hrow hcol R i hiA

  -- ゴールは「同じ Array・同じ index だが，index < size の証明だけ違う」2つの `get` の等式。
  -- `simp [hArr]` で配列の等式を流し込めば，証明引数は proof-irrelevant なので潰れる。
  simp [hArr]



/- clearPivotCol は pivot 行 `row` の Array 行を変更しない -/
lemma clearPivotCol_row_unchanged
  {m n K} [Field K]
  (R : Rectified m n K) {row col : Nat}
  (hrowA : row < R.A.size) (hcol : col < n) :
  (clearPivotCol R row col hcol).A[row]'(
    by
      have hsize := preserve_rowSize_clearPivotCol R row col hcol
      have : m = R.A.size := R.rowSize.symm
      simp [hsize, this, hrowA]
  ) = R.A[row] := by
  simp [R.rowSize] at hrowA
  have h :=
    clearPivotCol_loop_row_unchanged
      (m := m) (n := n)
      (row := row) (col := col)
      hrowA hcol R 0
  -- 定義展開
  simpa [clearPivotCol] using h



/- clearPivotCol は pivot 行 `row` の行ベクトルを変えない（matOf 版） -/
lemma clearPivotCol_pivot_row_unchanged
  {m n K} [Field K]
  (R : Rectified m n K) {row col : Nat}
  (hrow : row < m) (hcol : col < n) :
  (matOf (clearPivotCol R row col hcol)) ⟨row, by
    -- (clearPivotCol R …).A.size = m を使って row < m から証明
    have hsize := (clearPivotCol R row col hcol).rowSize
    -- hsize : (clearPivotCol R …).A.size = m
    simpa [hsize] using hrow
  ⟩
    =
  (matOf R) ⟨row, by
    -- R.A.size = m を使って row < m から row < R.A.size を作る
    have hsize := R.rowSize
    simpa [hsize] using hrow
  ⟩ := by
  -- 行ベクトルの等式なので、列方向に funext すれば十分
  funext j
  -- matOf の定義を展開
  -- 左辺：clearPivotCol 側
  have hsize' :
      (clearPivotCol R row col hcol).A.size = m :=
    (clearPivotCol R row col hcol).rowSize
  have hsizeR : R.A.size = m := R.rowSize

  -- それぞれの `matOf` の定義で使う hiA を用意
  have hrowA' : row < (clearPivotCol R row col hcol).A.size := by
    simpa [hsize'] using hrow
  have hrowA : row < R.A.size := by
    simpa [hsizeR] using hrow

  -- matOf の定義をそのまま書き下ろすと、
  --   matOf R ⟨row,_⟩ j = (R.A[row])[j]
  -- になるので、それを使って書き換える
  simp [matOf, toMat, clearPivotCol_row_unchanged R hrowA hcol]



/- clearPivotCol は pivot 成分が 1 なら、
  pivot 列の pivot 行以外を 0 にする -/
lemma clearPivotCol_pivot_col_other_rows_zero
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat)
  (hrow : row < m) (hcol : col < n)
  (hpiv : (matOf R)
            ⟨row, by
              -- row < m から row < R.A.size
              have hsize : R.A.size = m := by
                simpa using R.rowSize
              simpa [hsize] using hrow
            ⟩
            ⟨col, hcol⟩ = 1) :
  let R₃ := clearPivotCol R row col hcol
  ∀ i' : Fin m, i' ≠ ⟨row, hrow⟩ →
    (matOf R₃) i' ⟨col, hcol⟩ = 0 := by
  classical
  -- R₃ の定義を展開
  intro R₃ i' hi'
  -- R₃ = clearPivotCol R row col hcol = clearPivotCol_loop R row col hcol 0
  have hsize_R : R.A.size = m := by
    simpa using R.rowSize
  have hrowA : row < R.A.size := by
    simpa [hsize_R] using hrow

  -- row 番号の Fin
  let frow : Fin m := ⟨row, hrow⟩

  -- 行 index を Fin m にキャストし直す補助
  have hrow_cast :
    (⟨row, by simpa [hsize_R] using hrowA⟩ : Fin m) = frow := by
    simp [frow]

  -- 行列 R での pivot 成分 = 1 を、Fin m 版に書き直す
  have hpiv_fin :
    (matOf R) frow ⟨col, hcol⟩ = 1 := by
    -- hpiv は「row < R.A.size」を使った Fin で書いてあるので、
    -- それを cast してあげる
    have := hpiv
    -- R の rowSize から index の一致を使って書き換える
    -- （ここは simp で大抵落ちるはず）
    -- 実際の環境に合わせて微調整が必要かも
    simpa [frow, hsize_R] using this

  -- ループ不変式をまとめた強い帰納法 lemma
  have main :
    ∀ (k i : Nat) (R' : Rectified m n K),
      i + k = m →
      -- 不変式：R' のサイズは m、pivot 行 col 成分は 1、
      --         "すでに処理した行" (< i) の col 成分は 0
      (matOf R') frow ⟨col, hcol⟩ = 1 →
      (∀ j : Fin m, (j.val < i ∧ j ≠ frow) →
        (matOf R') j ⟨col, hcol⟩ = 0) →
      let R'' := clearPivotCol_loop R' row col hcol i
      (matOf R'') frow ⟨col, hcol⟩ = 1 ∧
      (∀ j : Fin m, (j.val < m ∧ j ≠ frow) →
        (matOf R'') j ⟨col, hcol⟩ = 0) := by
    intro k
    induction k with
    | zero =>
      -- 残りステップ k = 0 の場合： i + 0 = m ⇒ i = m
      intro i R' hmi hpiv' hcleared
      have hi : i = m := by
        simpa using hmi
      -- もうこれ以上ループは何もせず R' を返す
      -- clearPivotCol_loop R' ... m = R' （i < m が成り立たないので else branch）
      have hloop :
        clearPivotCol_loop R' row col hcol m = R' := by
        have : ¬ m < m := Nat.lt_irrefl _
        -- i = m の場合、if hi : i < m は false
        simp [clearPivotCol_loop]
      -- そのまま不変式を引き継ぐだけ
      refine And.intro ?h_piv ?h_all
      · -- pivot 行の pivot 成分は 1 のまま
        subst hi
        simpa [hloop] using hpiv'
      · -- すべての j ≠ frow, j < m で col 成分は 0
        intro j hj
        have hj_lt : j.val < m := hj.1
        have hj_ne : j ≠ frow := hj.2
        -- j.val < m = i & j ≠ frow なので hcleared が使える
        have h0 : (j.val < i ∧ j ≠ frow) := by
          conv =>
            arg 1
            rw [hi]
          simp [hj_lt, hj_ne]
        have hz : matOf R' j ⟨col, hcol⟩ = 0 := hcleared j h0
        subst hi
        simpa [hloop] using hz

    | succ k ih =>
      -- 残りステップ k+1：まだ処理する行が残っているケース
      intro i R' hmi hpiv' hcleared
      -- i + (k+1) = m ⇒ i < m
      have hi_lt : i < m := by
        -- もし i ≥ m なら i + (k+1) ≥ m + 1 になって矛盾
        by_contra hge
        have hge' : m ≤ i := Nat.le_of_not_gt hge
        have : m + 1 ≤ i + (k+1) := by
          have : m ≤ i + k := by
            have : i ≤ i + k := Nat.le_add_right i k
            exact Nat.le_trans hge' this
          exact Nat.succ_le_succ this
        -- でも hmi : i + (k+1) = m
        have : m + 1 ≤ m := by simp [← hmi] at this
        exact Nat.not_le_of_gt (Nat.lt_succ_self m) this
      -- clearPivotCol_loop の i ステップを 1 回展開
      have hstep :
        clearPivotCol_loop R' row col hcol i =
        if hi : i < m then
          let fi : Fin m := ⟨i, by simpa [R'.rowSize] using hi⟩
          if hrow_i : i = row then
            clearPivotCol_loop R' row col hcol (i+1)
          else
            let a : K := (matOf R') fi ⟨col, hcol⟩
            let R'' : Rectified m n K := rAxpy R' i row (-a)
            clearPivotCol_loop R'' row col hcol (i+1)
        else
          R' := by
        conv =>
          lhs
          unfold clearPivotCol_loop

      -- 以降、上の if の分岐ごとに場合分けする
      by_cases hrow_i : i = row
      · -- case 1: i = row → pivot 行はスキップして i+1 へ
        -- R'' = clearPivotCol_loop R' ... (i+1)
        have hR'' :
          clearPivotCol_loop R' row col hcol i =
          clearPivotCol_loop R' row col hcol (i+1) := by
          conv =>
            lhs
            unfold clearPivotCol_loop
          simp [hrow_i, hrow]

        -- i = row なので、「i 未満の行」は「pivot 行 row 以外」のみ
        -- pivot 行は不変なので、hpiv' と hcleared から不変式をそのまま i+1 に持ち上げられる
        -- i+1 + k = m で ih を使う
        have hmi' : (i+1) + k = m := by
          -- hmi : i + (k+1) = m から
          -- i + k.succ = i + k + 1
          -- を使って整理
          have := hmi
          have : i + k.succ = i.succ + k := by
            simp [Nat.add_comm, Nat.add_left_comm]
          -- i + k.succ = m なので
          calc
            (i.succ + k) = i + k.succ := this.symm
            _ = m := hmi

        -- i 未満の行はすべて col 成分 0 なので、
        -- i+1 未満の行も同じ条件を満たす（pivot 行 row は i と同じなので i 未満には現れない）
        have hcleared' :
          ∀ j : Fin m, (j.val < i.succ ∧ j ≠ frow) →
            (matOf R') j ⟨col, hcol⟩ = 0 := by
          intro j hj
          have hj_lt : j.val < i.succ := hj.1
          have hj_ne : j ≠ frow := hj.2
          -- j.val < i.succ ⇒ j.val ≤ i なので、「i 未満 or = i」に分かれる
          have hj_cases : j.val < i ∨ j.val = i := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj_lt)
          cases hj_cases with
          | inl hj_lt_i =>
            -- j.val < i かつ j ≠ frow なら hcleared がそのまま適用できる
            have h0 : (j.val < i ∧ j ≠ frow) := ⟨hj_lt_i, hj_ne⟩
            exact hcleared j h0
          | inr hj_eq_i =>
            -- j.val = i のとき：i = row なので j = frow になってしまい、
            -- hj_ne と矛盾する。従ってこの分岐は発生しない。
            have : j = frow := by
              -- Fin.ext で j と frow の val が等しいことから導く
              apply Fin.ext
              simp [frow, hj_eq_i, hrow_i]  -- val が row で一致
            exact (hj_ne this).elim

        -- i+1 の地点で ih を適用
        have hIH :=
          ih (i+1) R' hmi' hpiv' hcleared'

        -- clearPivotCol_loop R' ... i の結果 R'' と IH で使っている
        -- clearPivotCol_loop R' ... (i+1) を同一視しておく
        have hR''_IH :
          clearPivotCol_loop R' row col hcol (i+1) =
          clearPivotCol_loop R' row col hcol i := by
          simp [hR'']  -- hR'' の向きを合わせる

        -- goal: let R'' := clearPivotCol_loop R' ... i in ...
        -- の形を整理
        -- ここは `simp [hR'', hR''_IH]` でほぼそのまま IH を返せます
        -- （実際のゴールと IH の型を見て調整してください）
        -- 以下は少し手抜きの書き方：
        simpa [hR''] using hIH

      · -- case 2: i ≠ row → 行 i を pivot 行で掃き出す
        -- この場合は
        --   a := (matOf R') fi (col)
        --   R'' := rAxpy R' i row (-a)
        -- として i 行の col 成分を 0 にする
        have hi_ne_row : i ≠ row := hrow_i

        -- fi : Fin m, a : K, R'' : Rectified m n K
        have hiA : i < R'.A.size := by
          -- R'.A.size = m なので
          have hsize : R'.A.size = m := by
            simpa using (R'.rowSize)
          simpa [hsize] using hi_lt
        let fi : Fin m := ⟨i, by simpa [R'.rowSize] using hi_lt⟩
        let a : K := (matOf R') fi ⟨col, hcol⟩
        let R'' : Rectified m n K := rAxpy R' i row (-a)

        -- pivot 行の pivot 成分は rAxpy しても変わらない（src 行不変）
        have hrow_size' : row < R'.A.size := by
          -- R'.A.size = m と hrow から
          have hsize : R'.A.size = m := by
            simpa using (R'.rowSize)
          simpa [hsize] using hrow
        have h_dst_size' : i < R'.A.size := hiA

        have hpiv_R'' :
          (matOf R'') frow ⟨col, hcol⟩ = 1 := by
          -- まず Array レベルで「row 行は変わっていない」
          have hrow_eq :
            R''.A[row]'(
              by
                -- row < R''.A.size の証明
                have hsize_R' : R'.A.size = m := by
                  simpa using R'.rowSize
                have hrow_m : row < m := hrow
                have hsize_rowAxpy :=
                  preserve_rowSize_rowAxpy
                    R'.A R'.rowSize i row (-a)
                    (by simpa [hsize_R'] using hi_lt)
                    (by simpa [hsize_R'] using hrow_m)
                    R'.rect
                have hsize_R'' : R''.A.size = m := by
                  -- yes-branch の rAxpy なので size = m
                  unfold R''
                  -- `preserve_rowSize_rowAxpy` の結論をそのまま使うなら
                  -- simp 側は必要に応じて微調整してください
                  simpa [rAxpy, h_dst_size', hrow_size'] using hsize_rowAxpy
                -- これで row < R''.A.size
                simpa [hsize_R''] using hrow_m
            ) = R'.A[row] := by
            -- ここは素直に rAxpy_src_row_unchanged を使うだけで OK
            have h :=
              rAxpy_src_row_unchanged
                (R := R') (src := row) (dst := i)
                (hsrc := hrow_size') (hdst := hiA) (a := (-a)) hi_ne_row

            simp [R'', h]

          -- この Array の等式から、行ベクトル (matOf _) frow の等式を得る
          have hrow_mat :
            (matOf R'') frow = (matOf R') frow := by
            -- 列 j ごとに ext
            funext j
            -- matOf の定義が「i 行目は R.A[i] から作る」形になっているはずなので、
            -- hrow_eq で R''.A[row] を R'.A[row] に書き換えれば両辺同じになります。
            -- 実際の matOf の定義に合わせて simp の引数は調整してください。
            simp [matOf, toMat, frow, hrow_eq]

          -- この行ベクトルの等式から、col 成分の等式を取り出す
          have h :=
            congrArg (fun (r : Fin n → K) => r ⟨col, hcol⟩) hrow_mat

          -- 右辺は hpiv' = 1 なので、あとはこれでおしまい
          simpa [hpiv', frow] using h

        -- i 行の col 成分は rAxpy で 0 になることを確認
        have hcol_i_zero_R'' :
          (matOf R'') ⟨i, by simpa [R''.rowSize] using hi_lt⟩ ⟨col, hcol⟩ = 0 := by
          -- `fi` を Fin m として再確認
          have hi_fin :
              (⟨i, by simpa [R''.rowSize] using hi_lt⟩ : Fin m) = fi := by
            -- fi := ⟨i, by simpa [R'.rowSize] using hi_lt⟩ なので
            simp [fi]

          -- R'' を rAxpy の定義で展開
          unfold R''
          -- i 行・col 列の成分を rowAxpy の定義まで落とす
          -- ここでのキーは：dst = i の行は newRow になり、
          -- その newRow の col 成分が `ri[col] + (-a) * rk[col]` であること
          -- matOf, rowAxpy を unfold しつつ simp すると
          -- その形まで落ちます。
          -- 実際の matOf の定義に応じて `simp` の引数は微調整してください。
          simp [rAxpy, hiA, hrow_size', rowAxpy, matOf, fi, a,
          toMat, Array.setIfInBounds]
          simp [matOf, toMat, frow] at hpiv'
          simp [hpiv']
        -- i 行以外（j.val < i の行）は hcleared から 0 のまま、
        -- row 行は hpiv_R'' で pivot 成分 1 のまま、を不変式にして i+1 に進める。
        -- このあたりは case (1) とほぼ同様に ih を呼ぶだけなので、
        -- 省略します。
        have hloop_i :
            clearPivotCol_loop R' row col hcol i =
              clearPivotCol_loop R'' row col hcol (i+1) := by
            -- hi_lt : i < m, hrow_i : i ≠ row を使って if を潰す
            have hi : i < m := hi_lt
            conv =>
              lhs
              unfold clearPivotCol_loop
            simp [hi, hrow_i, fi, a, R'']
        have hmi' : (i+1) + k = m := by
          -- hmi : i + (k+1) = m から単に結合律・交換律で書き換え
          simpa [Nat.succ_eq_add_one,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmi
                  -- R'' に対する「i+1 未満の行は 0」の不変式を作る
        have hcleared'' :
          ∀ j : Fin m, (j.val < i.succ ∧ j ≠ frow) →
            matOf R'' j ⟨col, hcol⟩ = 0 := by
          intro j hj
          have hj_lt : j.val < i.succ := hj.1
          have hj_ne : j ≠ frow := hj.2
          have hj_le : j.val ≤ i := Nat.le_of_lt_succ hj_lt
          have hj_cases : j.val < i ∨ j.val = i :=
            lt_or_eq_of_le hj_le
          cases hj_cases with
          | inl hj_lt_i =>
            -- j.val < i のとき: 「古い行」なので hcleared と
            -- 「その行は rAxpy で変わらない」補題を使う
            have hz_R' : matOf R' j ⟨col, hcol⟩ = 0 :=
              hcleared j ⟨hj_lt_i, hj_ne⟩

            have hrow_eq :
              R''.A[j.val]'(by
                -- j.val < R''.A.size の証明 (size = m) は
                -- hDstSize, preserve_rowSize_rowAxpy と同様のやり方で作る
                have hsize_R' : R'.A.size = m := by
                  simpa using R'.rowSize
                have hsize_rowAxpy :=
                  preserve_rowSize_rowAxpy
                    R'.A R'.rowSize i row (-a)
                    (by simpa [hsize_R'] using hi_lt)
                    (by simpa [hsize_R'] using hrow)
                    R'.rect
                have hsize_R'' : R''.A.size = m := by
                  -- yes-branch の rAxpy なので size = m
                  unfold R''
                  simpa [rAxpy, hiA, hrow_size'] using hsize_rowAxpy
                have hj_m : j.val < m := by
                  simp
                simp [hsize_R'', hj_m]
              ) = R'.A[j.val]'(by
                -- j.val < R'.A.size の証明
                have hsize_R' : R'.A.size = m := by
                  simpa using R'.rowSize
                have hj_m : j.val < m := by
                  simp
                simp [hsize_R', hj_m]
              ) := by
              -- rAxpy_other_row_unchanged を使う想定
              have h :=
                rAxpy_other_row_unchanged
                  (R := R') (src := row) (dst := i)
                  (hsrc := hrow_size') (hdst := hiA)
                  (hj := by
                    -- j.val < R'.A.size の証明
                    have hsize_R' : R'.A.size = m := by
                      simpa using R'.rowSize
                    have hj_m : j.val < m := by
                      simp
                    simp [hsize_R']
                  )
                  (hjne := Nat.ne_of_lt hj_lt_i)
                  (a := -a)
              simp [R'', h]

            have hmat_eq :
              matOf R'' j ⟨col, hcol⟩ =
              matOf R' j ⟨col, hcol⟩ := by
              -- hrow_eq を matOf レベルに上げる（列ごとに ext / simp）
              simp [matOf, toMat, hrow_eq]

            simpa [hmat_eq] using hz_R'
          | inr hj_eq_i =>
            -- j.val = i のとき: まさに掃き出した行なので hcol_i_zero_R''
            have : j = ⟨i, hi_lt⟩ := by
              apply Fin.ext
              simp [hj_eq_i]
            subst this
            simpa using hcol_i_zero_R''
                  -- ここで IH を R'', i+1 に適用
        have hIH := ih (i+1) R'' hmi' hpiv_R'' hcleared''
        rcases hIH with ⟨hpiv_loop, hzeros_loop⟩

        refine And.intro ?h_piv_1 ?h_all_2
        · -- h_piv_1: pivot entry after step i is still 1
          -- i ステップ目のループ展開
          -- hloop_i で clearPivotCol_loop R' ... i と同一視
          have hpiv_goal :
            matOf (clearPivotCol_loop R' row col hcol i)
                  frow ⟨col, hcol⟩ = 1 := by
            simpa [hloop_i] using hpiv_loop

          exact hpiv_goal
        · -- h_all_2: all other entries in pivot column are zero
          intro j hj
          -- hzeros_loop は R'' 版についての主張：
          --   matOf (clearPivotCol_loop R'' ... (i+1)) j col = 0
          -- それを hloop_i で R' 版に引き戻す
          have hz :
            matOf (clearPivotCol_loop R'' row col hcol (i+1))
                  j ⟨col, hcol⟩ = 0 :=
            hzeros_loop j hj
          simpa [hloop_i] using hz
  -- ここまでで main ができたとして、i = 0, R' = R からスタート
  have hmain0 :
    let R'' := clearPivotCol_loop R row col hcol (0 : ℕ);
    (matOf R'') frow ⟨col, hcol⟩ = 1 ∧
    ∀ j : Fin m, (j.val < m ∧ j ≠ frow) →
      (matOf R'') j ⟨col, hcol⟩ = 0 := by
    have hmi : 0 + m = m := by simp
    have hcleared0 :
      ∀ j : Fin m, (j.val < 0 ∧ j ≠ frow) →
        (matOf R) j ⟨col, hcol⟩ = 0 := by
      intro j hj
      -- j.val < 0 は成り立たないので矛盾から何でも言える
      exact (Nat.not_lt_zero _ hj.1).elim
    simpa using main m 0 R hmi hpiv_fin hcleared0

  -- clearPivotCol = clearPivotCol_loop ... 0
  have hR₃ :
    clearPivotCol R row col hcol =
    clearPivotCol_loop R row col hcol 0 := rfl

  -- hmain0 から欲しい主張を取り出す
  -- let R₃ := clearPivotCol R ... を使う形に合わせる
  have hR₃_spec := hmain0
  -- R₃ に書き換え
  rcases hR₃_spec with ⟨hpiv_R₃, hcol_zero_R₃⟩

  -- 最終ゴール：R₃ の pivot 列の pivot 行以外は 0
  -- つまり hcol_zero_R₃ をそのまま使えばよい
  -- i' : Fin m, i' ≠ frow
  -- かつ i'.val < m は自明なので、それを渡す
  have hi_lt : i'.val < m := i'.is_lt
  have : i'.val < m ∧ i' ≠ frow := ⟨hi_lt, hi'⟩
  simpa [hR₃, frow] using hcol_zero_R₃ i' this


lemma rAxpy_dst_row_only
  {m n K} [Field K]
  (R : Rectified m n K)
  {src dst : Nat} (hsrc : src < R.A.size) (hdst : dst < R.A.size)
  {j : Nat} (hj : j < R.A.size) (h_ne : j ≠ dst) (a : K) :
  (rAxpy R dst src a).A[j]'(by
    -- j < (rAxpy R dst src a).A.size の証明（size = m）を作る
    have hsize : (rAxpy R dst src a).A.size = m := by
      -- これは preserve_rowSize_rowAxpy から出てくるはず
      have hsize' :=
        preserve_rowSize_rowAxpy R.A R.rowSize dst src a
          (
            by
              have hsizeA : R.A.size = m := R.rowSize
              simpa [hsizeA] using hdst
          )
          (
            by
              have hsizeA : R.A.size = m := R.rowSize
              simpa [hsizeA] using hsrc
          )
          R.rect
      simp [rAxpy, hsrc, hdst, hsize']
    -- これで j < (rAxpy R dst src a).A.size
    have : m = R.A.size := R.rowSize.symm
    simp [hsize, this, hj]
  ) = R.A[j]'(by
    -- j < R.A.size の証明は hj そのもの
    exact hj
  ) := by
  -- rAxpy の定義から、dst 行以外は set! されないのでそのまま
  unfold rAxpy
  -- yes-branch の if を潰す
  simp [hsrc, hdst, rowAxpy, Array.setIfInBounds, Array.getElem_set, h_ne.symm]


lemma matOf_rAxpy_other_row
  {m n K} [Field K]
  (R : Rectified m n K)
  {src dst : Nat} (hsrc : src < R.A.size) (hdst : dst < R.A.size)
  {i' : Fin m} (h_ne : i'.val ≠ dst) (a : K) :
  (matOf (rAxpy R dst src a)) i' =
  (matOf R) i' := by
  -- 各列ごとに ext
  funext j
  -- 両辺を配列レベルに展開
  -- （matOf の定義が `R.A[i'.val][j.val]` のはずなので `simp`）
  have hj : i'.val < R.A.size := by
    -- rowSize : R.A.size = m から
    have hsize : R.A.size = m := R.rowSize
    simp [hsize]
  have hj' : i'.val < (rAxpy R dst src a).A.size := by
    -- これも rowSize 保持補題から
    have hsize :=
      preserve_rowSize_rowAxpy R.A R.rowSize dst src a
        (
          by
            have hsizeA : R.A.size = m := R.rowSize
            simpa [hsizeA] using hdst
        )
        (
          by
            have hsizeA : R.A.size = m := R.rowSize
            simpa [hsizeA] using hsrc
        ) R.rect
    have : (rAxpy R dst src a).A.size = m := by
      simp [rAxpy, hsrc, hdst, hsize]
    simp [this]

  -- さっきの配列レベルの補題を使う
  have hrow :=
    rAxpy_dst_row_only (R := R)
      (hsrc := hsrc) (hdst := hdst)
      (j := i'.val) (hj := hj) (h_ne := h_ne) (a := a)

  -- これを matOf に翻訳
  simp [matOf, toMat, hrow]


lemma matOf_rAxpy_dst_row_left_col
  {m n K} [Field K]
  (R : Rectified m n K)
  {src dst : Nat} (hsrc : src < R.A.size) (hdst : dst < R.A.size)
  (j : Fin n)
  (h_pivot_left0 :
    (matOf R) ⟨src, by
      have hsize : R.A.size = m := R.rowSize
      simpa [hsize] using hsrc
    ⟩ j = 0)
  (a : K) :
  (matOf (rAxpy R dst src a)) ⟨dst, by
    have : dst < m := by simpa [R.rowSize] using hdst
    -- rowSize 保持から (rAxpy R ...).A.size = m
    -- を使って dst < (rAxpy R ...).A.size にする
    -- （ここも `preserve_rowSize_rowAxpy` から `simp` で落とす）
    exact this
  ⟩ j =
  (matOf R) ⟨dst, by
    have hsize : R.A.size = m := R.rowSize
    simpa [hsize] using hdst
  ⟩ j := by
  -- rAxpy / rowAxpy / matOf を unfold すれば
  -- 対象の成分は `ri[j] + a * rk[j]` という形になっているはずなので，
  -- h_pivot_left0 を使って `rk[j] = 0` として消す。
  -- だいたいこんな感じ：
  unfold rAxpy
  simp [hsrc, hdst, rowAxpy, matOf]  -- newRow[j] = old + a * pivot
  -- ここで pivot の j 成分を `h_pivot_left0` で 0 にする
  -- （必要なら matOf → Array の書き換えを `simp [matOf]` で）
  have := h_pivot_left0
  simp [matOf, toMat] at this

  simp [toMat, this]  -- a * 0 = 0, old + 0 = old

lemma matOf_rAxpy_dst_row
  {m n K} [Field K]
  (R : Rectified m n K) {i k : Nat}
  (hi : i < m) (hk : k < m) (a : K) (c : Fin n) :
  matOf (rAxpy R i k a) ⟨i, hi⟩ c
    = matOf R ⟨i, hi⟩ c + a * matOf R ⟨k, hk⟩ c := by
  unfold matOf rAxpy rowAxpy toMat
  simp [R.rowSize]
  simp [hi, hk]


lemma matOf_rAxpy_other_row'
  {m n K} [Field K]
  (R : Rectified m n K) {i k : Nat}
  (hi : i < m) (hk : k < m)
  {r : Fin m} (hne : (r : ℕ) ≠ i) (a : K) (c : Fin n) :
  matOf (rAxpy R i k a) r c = matOf R r c := by
  unfold matOf rAxpy rowAxpy toMat
  simp [R.rowSize, hi, hk, Array.setIfInBounds, hne.symm]

/- `clearPivotCol` は pivot 列より左の列 `j < col` を一切変えない。 -/
lemma clearPivotCol_preserves_left_cols
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hcol : col < n)
  (h_row_lt_m : row < m)
  (h_pivot_left0 :
    ∀ j : Fin n, (j : ℕ) < col →
      (matOf R) ⟨row, h_row_lt_m⟩ j = 0) :
  ∀ (i' : Fin m) (j : Fin n), (j : ℕ) < col →
    (matOf (clearPivotCol R row col hcol)) i' j =
    (matOf R) i' j := by
  -- row の Fin 版
  let frow : Fin m := ⟨row, h_row_lt_m⟩

  -- 強い帰納法：k = m - i
  have main :
    ∀ (k i : Nat) (R' : Rectified m n K),
      i + k = m →
      -- 不変式１：左側列は元の R と同じ
      (∀ (i' : Fin m) (j : Fin n), (j : ℕ) < col →
        (matOf R') i' j = (matOf R) i' j) →
      -- 不変式２：pivot 行の左側列は 0
      (∀ j : Fin n, (j : ℕ) < col →
        (matOf R') frow j = 0) →
      let R'' := clearPivotCol_loop R' row col hcol i
      (∀ (i' : Fin m) (j : Fin n), (j : ℕ) < col →
        (matOf R'') i' j = (matOf R) i' j) ∧
      (∀ j : Fin n, (j : ℕ) < col →
        (matOf R'') frow j = 0) := by
    intro k
    induction k with
    | zero =>
      intro i R' hmi h_inv h_piv
      have hi : i = m := by simpa using hmi
      -- i = m のとき clearPivotCol_loop R' ... m = R'
      have hloop : clearPivotCol_loop R' row col hcol m = R' := by
        simp [clearPivotCol_loop]  -- if hi : m < m is false
      -- 左側列は不変式そのまま
      refine And.intro ?h_eq ?h_piv'
      · -- 左側列はそのまま
        intro i' j hj
        -- R'' = R' なので h_inv をそのまま使えばよい
        have := h_inv i' j hj
        -- R'' を clearPivotCol_loop ... m に戻してから hloop で R' に戻す
        -- i = m を使って R'' の定義も m に書き換える
        simpa [hi, hloop] using this
      · -- pivot 行の左側も 0 のまま
        intro j hj'
        have := h_piv j hj'
        simpa [hi, hloop] using this

    | succ k ih =>
      intro i R' hmi h_inv h_piv
      -- i + (k+1) = m なら i < m
      have hi_lt : i < m := by
        by_contra hge
        have hge' : m ≤ i := Nat.le_of_not_gt hge
        have : m + 1 ≤ i + (k+1) := by
          have : m ≤ i + k := by
            have : i ≤ i + k := Nat.le_add_right i k
            exact Nat.le_trans hge' this
          exact Nat.succ_le_succ this
        have : m + 1 ≤ m := by simp [← hmi] at this
        exact Nat.not_le_of_gt (Nat.lt_succ_self m) this

      -- 1 ステップ分展開
      have hstep :
        clearPivotCol_loop R' row col hcol i =
        if hi : i < m then
          let fi : Fin m := ⟨i, by simpa [R'.rowSize] using hi⟩
          if hrow_i : i = row then
            clearPivotCol_loop R' row col hcol (i+1)
          else
            let a : K := (matOf R') fi ⟨col, hcol⟩
            let R'' : Rectified m n K := rAxpy R' i row (-a)
            clearPivotCol_loop R'' row col hcol (i+1)
        else
          R' := by
        conv => lhs; unfold clearPivotCol_loop

      by_cases hrow_i : i = row
      · ----------------------------------------------------------------
        -- case 1: i = row → pivot 行はスキップして i+1 へ
        ----------------------------------------------------------------
        have hR'' :
          clearPivotCol_loop R' row col hcol i =
          clearPivotCol_loop R' row col hcol (i+1) := by
          have hi : i < m := hi_lt
          conv =>
            lhs
            unfold clearPivotCol_loop
            simp [hi, hrow_i, h_row_lt_m]
          conv =>
            rhs
            simp [hrow_i]

        -- i+1 + k = m
        have hmi' : (i+1) + k = m := by
          -- i + (k+1) = m から
          simpa [Nat.succ_eq_add_one,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmi

        -- i+1 未満の行についての不変式は h_inv から継承
        have h_inv' :
          ∀ i' : Fin m, ∀ j : Fin n, (j : ℕ) < col →
            (matOf R') i' j = (matOf R) i' j := h_inv
        have h_piv' :
          ∀ j : Fin n, (j : ℕ) < col →
            (matOf R') frow j = 0 := h_piv

        have hIH := ih (i+1) R' hmi' h_inv' h_piv'
        simp
        refine And.intro ?h1 ?h2
        · -- left cols same as R
          intro i' j hj
          have := hIH.1 i' j hj
          -- R'' を clearPivotCol_loop ... (i+1) に戻してから hR'' で R' に戻す
          simpa [hR''] using this
        · -- pivot row left cols zero
          intro j hj
          have := hIH.2 j hj
          simpa [hR''] using this

      · ----------------------------------------------------------------
        -- case 2: i ≠ row → 行 i を pivot 行で掃き出す
        ----------------------------------------------------------------
        have hi_ne_row : i ≠ row := hrow_i
        -- インデックス関係
        have hiA : i < R'.A.size := by
          have hsize : R'.A.size = m := by simpa using R'.rowSize
          simpa [hsize] using hi_lt
        have hrowA : row < R'.A.size := by
          have hsize : R'.A.size = m := by simpa using R'.rowSize
          simpa [hsize] using h_row_lt_m

        -- fi, a, R''
        let fi : Fin m := ⟨i, by simpa [R'.rowSize] using hi_lt⟩
        let a  : K := (matOf R') fi ⟨col, hcol⟩
        let R'' : Rectified m n K := rAxpy R' i row (-a)

        -- R'' に対しても「pivot 行左側は 0」「左側列は元の R と同じ」を示す

        -- pivot 行左側 0：src 行は変わらない ＋ h_piv
        have h_piv_R'' :
          ∀ j : Fin n, (j : ℕ) < col →
            (matOf R'') frow j = 0 := by
          intro j hj
          have hrow_eq :=
            rAxpy_src_row_unchanged
              (R := R') (src := row) (dst := i)
              (hsrc := hrowA) (hdst := hiA) (a := -a)
          -- matOf レベルに持ち上げて、h_piv を使う
          -- （詳細は rAxpy_src_row_unchanged の型に合わせて調整）
          have hrow_mat :
            (matOf R'') frow = (matOf R') frow := by
            funext j'
            simp [matOf, R'', rAxpy, rowAxpy, toMat,
            hiA, hrowA, Array.setIfInBounds, Array.getElem_set]
            have : i ≠ frow.val := hi_ne_row
            simp [this]
          have := congrArg (fun r => r j) hrow_mat
          -- R' 側の pivot 左列は 0
          have hz := h_piv j hj
          simpa [hz] using this

        -- 左側列が R と同じ：行ごとに分けて処理
        have h_inv_R'' :
          ∀ i' : Fin m, ∀ j : Fin n, (j : ℕ) < col →
            (matOf R'') i' j = (matOf R) i' j := by
          intro i' j hj
          by_cases hdst' : (i' : Nat) = i
          · -- 行 i: new_i[j] = old_i[j] + (-a) * pivot_row[j] で pivot_row[j]=0
            -- pivot 行左列 0 ＋ h_inv を使って new = old
            have h_piv0 :
              (matOf R') frow j = 0 := h_piv j hj
            have h_old :
              (matOf R') ⟨i, hi_lt⟩ j = (matOf R) ⟨i, hi_lt⟩ j :=
              h_inv ⟨i, hi_lt⟩ j hj
            -- ここで matOf_rAxpy_dst_row_left_col を使って
            have hdst :=
              matOf_rAxpy_dst_row_left_col
                (R := R')
                (src := row) (dst := i)
                (hsrc := hrowA) (hdst := hiA)
                (j := j)
                (h_pivot_left0 :=
                  by
                    -- R' の pivot 左側 = R の pivot 左側 = 0
                    -- h_inv と h_piv から引っ張る
                    have := h_piv j hj
                    have := congrArg id this
                    simpa using this)
                (a := -a)
            -- R'' 側の i 行 j 列 = R' 側の i 行 j 列 = R 側の i 行 j 列
            have := congrArg id hdst
            subst hdst'
            simpa [h_old] using this
          · -- 行 i 以外: rAxpy_other_row_unchanged
            have hi_ne : i'.val ≠ i := hdst'
            have hrow_eq :=
              matOf_rAxpy_other_row
                (R := R') (src := row) (dst := i)
                (hsrc := hrowA) (hdst := hiA)
                (i' := i') (h_ne := hi_ne) (a := -a)
            have h_old := h_inv i' j hj
            simp [R'', hrow_eq, h_old]
        -- ここで IH を R'', i+1 に適用
                -- ここで IH を R'', i+1 に適用
        have hmi' : (i+1) + k = m := by
          simpa [Nat.succ_eq_add_one,
                Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmi
        have hIH := ih (i+1) R'' hmi' h_inv_R'' h_piv_R''

        -- hIH の `let R'' := ...` を消して、見やすい型にする
        have hIH' :
          (∀ (i' : Fin m) (j : Fin n), (j : ℕ) < col →
              matOf (clearPivotCol_loop R'' row col hcol (i+1)) i' j = matOf R i' j)
          ∧
          (∀ (j : Fin n), (j : ℕ) < col →
              matOf (clearPivotCol_loop R'' row col hcol (i+1)) frow j = 0) := by
          simpa using hIH

        rcases hIH' with ⟨h_inv_after, h_piv_after⟩

                -- ここから main の結論を構成する部分
        -- clearPivotCol_loop R' ... i と R'' ... (i+1) の同一視
        have hloop_i :
          clearPivotCol_loop R' row col hcol i =
          clearPivotCol_loop R'' row col hcol (i+1) := by
          have hi : i < m := hi_lt
          conv =>
            lhs
            unfold clearPivotCol_loop
            simp [hi, hrow_i, fi, a, R'']

        -- 目標：
        -- let R₀ := clearPivotCol_loop R' row col hcol i in
        --   (∀ i' j, j < col → matOf R₀ i' j = matOf R i' j) ∧
        --   (∀ j, j < col → matOf R₀ frow j = 0)
        refine And.intro ?h_inv_final ?h_piv_final

        · -- h_inv_final : 左側列は R と一致
          intro i' j hj
          -- h_inv_after は R'' 側の結果
          have h := h_inv_after i' j hj
          -- hloop_i で R' 側の行列に書き戻す
          simpa [hloop_i] using h

        · -- h_piv_final : pivot 行左側は 0
          intro j' hj'
          have h := h_piv_after j' hj'
          simpa [hloop_i] using h


  -- main を i = 0, R' = R に適用
  have hmi0 : 0 + m = m := by simp
  have h_inv0 :
    ∀ i' j, (j : Fin n) < col →
      (matOf R) i' j = (matOf R) i' j := by
    intro i' j hj; rfl

  have hmain0 := main m 0 R hmi0 h_inv0 h_pivot_left0

  -- clearPivotCol = clearPivotCol_loop ... 0
  have hR₃ :
    clearPivotCol R row col hcol =
      clearPivotCol_loop R row col hcol 0 := rfl

  -- ゴール

  have h_eq_all := hmain0.1  -- (∀ i' j, ...) 部分を取り出す

  exact h_eq_all


/- 行 i に 行 k の a 倍を足す基本行列: (1 + a * E_{ik}) -/
def rAxpyMatrix
  {m K} [Field K]
  (i k : Fin m) (a : K)
  : Matrix (Fin m) (Fin m) K :=
  1 + Matrix.single i k a

/- i ≠ k のとき、基本行列の逆行列は a を -a にしたもの -/
lemma isUnit_rAxpyMatrix
  {m K} [Field K]
  (i k : Fin m) (a : K) (hik : i ≠ k) :
    IsUnit (rAxpyMatrix i k a) := by
  let E := rAxpyMatrix i k a
  let E_inv := rAxpyMatrix i k (-a)
  have h_add : Matrix.single i k a + Matrix.single i k (-a) = 0 := by
    simp [(Matrix.single_add i k a (-a)).symm]
  have h_add' : Matrix.single i k (-a) + Matrix.single i k a = 0 := by
    conv =>
      lhs
      simp [add_comm]
    exact h_add
  have h_sq : single i k a * single i k (-a) = 0 :=
    Matrix.single_mul_single_of_ne (c:=a) (i:=i) (j:=k) (k:=i) (h:=hik.symm) (d:=-a)
  have h_sq' : Matrix.single i k (-a) * Matrix.single i k a = 0 :=
    Matrix.single_mul_single_of_ne (c:=-a) (i:=i) (j:=k) (k:=i) (h:=hik.symm) (d:=a)
  have h_mul : E * E_inv = 1 := by
    simp [E, E_inv, rAxpyMatrix]
    -- (1 + A)(1 + B) = 1 + A + B + AB
    rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one]
    -- A + B = a * e_ik + (-a) * e_ik = 0
    conv =>
      lhs
      arg 2
      simp [h_sq]
    conv =>
      lhs
      arg 1
      simp
    simp [add_comm]
    conv =>
      lhs
      simp [<-add_assoc]
      arg 1
      rw [h_add]
    simp

  refine ⟨⟨E, E_inv, h_mul, ?_⟩, rfl⟩
  -- 左逆も同様
  simp [E, E_inv, rAxpyMatrix]
  rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one]
  simp [h_sq', add_assoc, h_add]

/- 行列積の成分計算: (E * A) r c の挙動 -/
lemma rAxpyMatrix_mul_apply
  {m n K} [Field K]
  (A : Matrix (Fin m) (Fin n) K)
  (i k : Fin m) (a : K) (r : Fin m) (c : Fin n) :
    (Matrix.mulᵣ (rAxpyMatrix i k a)  A) r c =
      if r = i then A i c + a * A k c else A r c := by
  conv => lhs; simp
  rw [rAxpyMatrix, Matrix.add_mul, Matrix.one_mul]
  dsimp
  split_ifs with h
  · rw [h]; simp
  · simp
    exact Matrix.single_mul_apply_of_ne a i k r c h A

------------------------------------------------------------------
-- 4. メインの補題: matOf_rAxpy
------------------------------------------------------------------

lemma matOf_rAxpy
  {m n K} [Field K]
  (R : Rectified m n K) {i k : Nat}
  (hi : i < m) (hk : k < m) (hik : i ≠ k) (a : K) :
  ∃ (E : Matrix (Fin m) (Fin m) K),
    IsUnit E ∧
    matOf (rAxpy R i k a) = Matrix.mulᵣ E (matOf R) := by
  classical
  -- Fin index
  let fi : Fin m := ⟨i, hi⟩
  let fk : Fin m := ⟨k, hk⟩
  let E := rAxpyMatrix fi fk a

  -- 1. IsUnit の証明 (先ほどの補題を使用)
  have hE_unit : IsUnit E := by
    apply isUnit_rAxpyMatrix
    intro h_eq
    apply hik
    injection h_eq

  -- 2. 作用結果の一致
  have hE_action : matOf (rAxpy R i k a) = Matrix.mulᵣ E (matOf R) := by
    ext r c
    -- 右辺の挙動
    let A := matOf R
    have h_right : (Matrix.mulᵣ E  A) r c = if r = fi then A fi c + a * A fk c else A r c := by
      apply rAxpyMatrix_mul_apply

    -- 左辺の挙動
    have h_left : matOf (rAxpy R i k a) r c =
        (if r = fi then A fi c + a * A fk c else A r c) := by
      by_cases hri : r = fi
      · rw [if_pos hri]
        subst hri
        apply matOf_rAxpy_dst_row (hi:=hi) (hk:=hk)
      · rw [if_neg hri]
        have hne : (r : ℕ) ≠ i := fun h => hri (Fin.ext h)
        apply matOf_rAxpy_other_row' (hi:=hi) (hk:=hk) (hne:=hne)

    rw [h_right, h_left]

  exact ⟨E, hE_unit, hE_action⟩


/-
  clearPivotCol_loop の作用が、ある可逆行列 E を左から掛けることと等しいことを示す補題。
  帰納法のために m - i の値 (len) で一般化して証明します。
-/
lemma matOf_clearPivotCol_loop
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hrow : row < m) (hcol : col < n) (i : Nat) :
  ∃ (E : Matrix (Fin m) (Fin m) K),
    IsUnit E ∧
    matOf (clearPivotCol_loop R row col hcol i) = Matrix.mulᵣ E (matOf R) := by
  -- ループの停止条件である m - i を len と置き、len に関する帰納法で証明する
  generalize h_len : m - i = len
  induction len generalizing i R with
  | zero =>
    -- ■ Base case: len = 0 つまり i >= m の場合
    -- ループは終了し、R をそのまま返す。対応する行列は単位行列 1。
    exists 1
    constructor
    · exact isUnit_one
    · -- clearPivotCol_loop の定義を展開
      rw [clearPivotCol_loop]
      -- i < m が False であることを示す
      have hi_not : ¬(i < m) := by
        -- m - i = 0 implies i >= m
        omega
      simp [hi_not]

  | succ len' ih =>
    -- ■ Step case: len = len' + 1 つまり i < m の場合
    -- ループは続く
    have hi : i < m := by omega

    -- ループを1回展開
    rw [clearPivotCol_loop]
    simp [hi]

    -- i = row かどうかで分岐
    by_cases hrow_eq : i = row
    · -- case 1: i = row (pivot行なのでスキップ)
      simp [hrow_eq]
      -- 再帰呼び出し: clearPivotCol_loop R ... (i + 1)
      -- 帰納法の仮定 (ih) を適用するための準備
      have h_len_next : m - (i + 1) = len' := by omega

      -- IH を適用 (R は変わらない)
      obtain ⟨E_next, hE_next_unit, h_action⟩ := ih R (i + 1) h_len_next

      exists E_next
      simp [hrow_eq] at h_action
      exact ⟨hE_next_unit, h_action⟩

    · -- case 2: i ≠ row (掃き出し実行)
      simp [hrow_eq]
      -- 変数定義
      let fi : Fin m := ⟨i, by simpa [R.rowSize] using hi⟩
      let a : K := (matOf R) fi ⟨col, hcol⟩
      let R' := rAxpy R i row (-a)

      -- 1. まず、このステップ単体で行列 E_step が掛かることを確認 (matOf_rAxpy を利用)


      have h_step : ∃ E_step, IsUnit E_step ∧ matOf R' = Matrix.mulᵣ E_step (matOf R) := by
        exact matOf_rAxpy R hi hrow hrow_eq (-a)

      obtain ⟨E_step, hE_step_unit, hR'_eq⟩ := h_step

      -- 2. 再帰部分 (残り) に帰納法を適用
      --    R が R' に変わっていることに注意
      have h_len_next : m - (i + 1) = len' := by omega
      obtain ⟨E_rest, hE_rest_unit, h_final⟩ := ih R' (i + 1) h_len_next

      -- 3. 全体の行列 E = E_rest * E_step を構成
      exists E_rest * E_step
      constructor
      · -- 可逆行列の積は可逆
        exact IsUnit.mul hE_rest_unit hE_step_unit
      · -- 作用の結合: final = E_rest * (matOf R') = E_rest * (E_step * matOf R)
        rw [h_final, hR'_eq]
        rw [Matrix.mul_assoc]
        simp

lemma matOf_clearPivotCol
  {m n K} [Field K]
  (R : Rectified m n K) (row col : Nat) (hrow : row < m) (hcol : col < n) :
  ∃ (E : Matrix (Fin m) (Fin m) K),
    IsUnit E ∧
    matOf (clearPivotCol R row col hcol) = Matrix.mulᵣ E (matOf R) := by
  -- clearPivotCol = loop R ... 0
  dsimp [clearPivotCol]
  -- さっきのループ版補題を i = 0 で使う
  simpa using matOf_clearPivotCol_loop R row col hrow hcol 0

lemma extendPivot_old
  {r n} (p : Fin r → Fin n) (newCol : Fin n)
  {i : Fin (r + 1)} (hi : (i : ℕ) < r) :
  extendPivot p newCol i = p ⟨i, hi⟩ := by
  unfold extendPivot
  simp [hi]

lemma matOf_rScale_pivot
  {m n K} [Field K]
  (R : Rectified m n K) (row : Nat) (hrow : row < m) (k : K)
  (j : Fin n) :
  matOf (rScale R row k) ⟨row, hrow⟩ j =
    k * matOf R ⟨row, hrow⟩ j := by
  -- rScale の定義を展開
  unfold rScale
  -- R.A.size = m を使って if のガードを true にする
  have hrowA : row < R.A.size := by
    have hsize : R.A.size = m := R.rowSize
    simpa [hsize] using hrow
  -- if_pos に落として、あとは rowScale 用の補題で落とす
  simp [hrowA, matOf, rowScale,
  Array.setIfInBounds, toMat]


lemma inv_step_some
  {m n K} [Field K] {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (hsome : findPivot_spec st hcol = some i0)
  : let R₁ := rSwap st.R st.rowCount i0.val
    let a  := (matOf R₁) ⟨st.rowCount, by
      -- rowCount < m を作る
      have h_pivot :=
        findPivot_spec_some_sound (st := st) (hcol := hcol) hsome
      rcases h_pivot with ⟨h_row_le_i0, _⟩
      exact lt_of_le_of_lt h_row_le_i0 i0.is_lt
    ⟩ ⟨st.colPtr, hcol⟩
    let R₂ := rScale R₁ st.rowCount (a⁻¹)
    let R₃ := clearPivotCol R₂ st.rowCount st.colPtr hcol
    let new_r   := st.rowCount + 1
    let new_c   := st.colPtr + 1
    let new_piv := extendPivot st.pivot ⟨st.colPtr, hcol⟩
    Inv st.M0 R₃ new_r new_c new_piv := by
  classical
  -- pivot の性質
  have h_pivot :=
    findPivot_spec_some_sound (st := st) (hcol := hcol) hsome
  rcases h_pivot with ⟨h_row_le_i0, h_nz⟩
  -- rowCount < m の証明（a の row インデックス用）
  have h_row_lt_m : st.rowCount < m :=
    lt_of_le_of_lt h_row_le_i0 i0.is_lt
  -- R₁, R₂, R₃, new_r, new_c, new_piv の定義
  let R₁ := rSwap st.R st.rowCount i0.val
  let a  := (matOf R₁) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩
  let R₂ := rScale R₁ st.rowCount (a⁻¹)
  let R₃ := clearPivotCol R₂ st.rowCount st.colPtr hcol
  let new_r   := st.rowCount + 1
  let new_c   := st.colPtr + 1
  let new_piv := extendPivot st.pivot ⟨st.colPtr, hcol⟩
  -- R₁ についての Inv
  have hInv_R₁ :
    Inv st.M0 R₁ st.rowCount st.colPtr st.pivot := by
    -- rSwap の補題
    have : st.rowCount ≤ i0 := h_row_le_i0
    exact inv_after_rSwap (st := st) this

  have h_swap :
    (matOf R₁) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ =
    (matOf st.R) i0 ⟨st.colPtr, hcol⟩ := by
    -- さっきの一般補題をそのまま使う
    have hi0_lt_m : (i0 : Nat) < m := i0.is_lt
    -- i0 は Fin m なので、上の lemma に cast して使う
    simpa [R₁] using
      (matOf_rSwap_row_left (R := st.R)
        (i := st.rowCount) (j := i0.val)
        (hi := h_row_lt_m) (hj := hi0_lt_m)
        (c := ⟨st.colPtr, hcol⟩))


  -- a ≠ 0 を確認（rSwap で rowCount 行と i0 行を入れ替えているはず）
  have ha_ne : a ≠ 0 := by
    unfold a
    intro hz
    apply h_nz
    have := congrArg id hz
    simpa [h_swap] using this


  -- R₂ についての Inv（rowCount, colPtr, pivot はまだ同じ）
  have hInv_R₂ :
    Inv st.M0 R₂ st.rowCount st.colPtr st.pivot := by
    have hrow_lt_m : st.rowCount < m :=
      lt_of_le_of_lt h_row_le_i0 i0.is_lt
    exact inv_after_rScale
      (R := R₁) (M0 := st.M0)
      (r0 := st.rowCount) (c0 := st.colPtr) (p0 := st.pivot)
      hInv_R₁ (a := a⁻¹) (
        by
          intro ha0
          apply ha_ne
          have := congrArg id ha0
          simpa using this
      ) hrow_lt_m
  -- ここから R₂, new_r, new_c, new_piv で Inv を作る
  -- 実際には hInv_R₂ と findPivot_spec_some_min / eq_some_iff を組み合わせて
  -- I1_bound, I1_mono, I1_in, I2_unit, I3_left0, I4_tail0, I5_fac をすべて埋めます。
  -- これは inv_init / inv_step_none と同じようにレコードを組み立てる形です。
  have hInv_step :
    Inv st.M0 R₃ (st.rowCount + 1) (st.colPtr + 1)
      (extendPivot st.pivot ⟨st.colPtr, hcol⟩) := by
    -- ★ ここが本体。extendPivot_strictMono_state, extendPivot_in,
    --    findPivot_spec_eq_some_iff などを総動員する場所。
    classical
    -- IsFirstPivotIndex の事実を取り出す
    have hFirst : IsFirstPivotIndex st hcol i0 :=
      (findPivot_spec_eq_some_iff st hcol i0).1 hsome

    have h_row_le_i0 : (st.rowCount : Nat) ≤ i0 := hFirst.1
    have h_nz : (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 := hFirst.2.1

    let hInv_R₂' := hInv_R₂

    rcases hInv_R₂ with
      ⟨h_rows_R₂, h_rect_R₂, h_bound_R₂,
        h_mono_R₂, h_in_R₂, h_unit_R₂,
        h_left0_R₂, h_tail0_R₂, h_fac_R₂⟩
    -- 各成分を構成
    have h_rows_R₃ : R₃.A.size = m := by
    -- R₃ = clearPivotCol R₂ ...
      simpa [R₃, clearPivotCol] using
        preserve_rowSize_clearPivotCol R₂ st.rowCount st.colPtr hcol


    have h_rect_R₃ : Rect R₃.A n := by
      simpa [R₃, clearPivotCol] using
        preserve_rect_clearPivotCol R₂ st.rowCount st.colPtr hcol
      -- 既存 Inv から row/col の境界
    have h_row_le_m : st.rowCount ≤ m := h_bound_R₂.1
    have h_col_le_n : st.colPtr ≤ n := h_bound_R₂.2

    -- すでに findPivot_spec_some_sound から rowCount < m は持っている
    have h_row_lt_m : st.rowCount < m := h_row_lt_m  -- すでに定義済

    have h_col_lt_n : st.colPtr < n := hcol

    have h_new_r_le_m : new_r ≤ m := by
      -- new_r = st.rowCount + 1
      -- rowCount < m から succ_le_of_lt で
      have : st.rowCount.succ ≤ m := Nat.succ_le_of_lt h_row_lt_m
      simpa [new_r] using this

    have h_new_c_le_n : new_c ≤ n := by
      have : st.colPtr.succ ≤ n := Nat.succ_le_of_lt h_col_lt_n
      simpa [new_c] using this

    have h_bound_R₃ : new_r ≤ m ∧ new_c ≤ n :=
      ⟨h_new_r_le_m, h_new_c_le_n⟩

      -- StrictMono は extendPivot_strictMono_state から
    have h_mono_R₃ :
      StrictMono (extendPivot st.pivot ⟨st.colPtr, hcol⟩) :=
      extendPivot_strictMono_state (st := st) hcol

    -- 各 pivot 列 < new_c は extendPivot_in から
    have h_in_R₃ :
      ∀ i, extendPivot st.pivot ⟨st.colPtr, hcol⟩ i < new_c := by
      intro i
      -- extendPivot_in は < st.colPtr + 1 を保証している想定
      simpa [new_c] using (extendPivot_in (st := st) hcol i)

    have h_fac_R₃ :
      ∃ (E : Matrix (Fin m) (Fin m) K),
        IsUnit E ∧ matOf R₃ = E * st.M0 := by
      rcases h_fac_R₂ with ⟨E0, hE0_unit, hE0_mul⟩

      rcases matOf_clearPivotCol R₂ st.rowCount st.colPtr h_row_lt_m hcol with
        ⟨E1, hE1_unit, hE1_mul⟩
      -- matOf R₃ = E1 * matOf R₂ = E1 * (E0 * M0) = (E1 * E0) * M0
      refine ⟨E1 * E0, ?_, ?_⟩
      · -- IsUnit (E1 ⬝ E0)
        exact IsUnit.mul hE1_unit hE0_unit
      · -- matOf R₃ = (E1 ⬝ E0) * M0
        calc
          matOf R₃
              = Matrix.mulᵣ E1 (matOf R₂) := hE1_mul
          _ = Matrix.mulᵣ E1 (Matrix.mulᵣ E0 st.M0) := by simp [hE0_mul]
          _ = Matrix.mulᵣ (Matrix.mulᵣ E1 E0) st.M0 := by simp [Matrix.mul_assoc]
        simp

    -- 「pivot 行 rowCount も R₂ と同じ」
    have h_pivot_row_unchanged :
      (matOf R₃) ⟨st.rowCount, h_row_lt_m⟩ =
      (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ := by
      simpa [R₃] using
        clearPivotCol_pivot_row_unchanged
          (R := R₂) (row := st.rowCount) (col := st.colPtr) (hrow := h_row_lt_m) (hcol := hcol)

    -- 「pivot 列 st.colPtr で pivot 行以外は 0」
    -- pivot 行 (rowCount) の pivot 成分は R₂ では 1
    have h_unit_piv_R₂ :
      (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ = 1 := by
      -- rScale の matOf 用補題で pivot 行の成分を展開
      have hscale :
        (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ =
          (a⁻¹) * (matOf R₁) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ := by
        -- R₂ = rScale R₁ st.rowCount (a⁻¹) を使って書き換え
        simpa [R₂] using
          (matOf_rScale_pivot
            (R := R₁)
            (row := st.rowCount)
            (hrow := h_row_lt_m)
            (k := a⁻¹)
            (j := ⟨st.colPtr, hcol⟩))

      -- a の定義はちょうど R₁ の (rowCount, colPtr) 成分
      have hR₁_piv :
        (matOf R₁) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ = a := by
        -- a はその成分として定義してあるので simp で終わる
        simp [a]

      -- 右辺を a⁻¹ * a に書き換える
      have hscale' :
        (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ =
          a⁻¹ * a := by
        simpa [hR₁_piv] using hscale

      -- Field なので a ≠ 0 から a⁻¹ * a = 1
      have hmul : a⁻¹ * a = (1 : K) := by
        -- `simp [ha_ne]` で大抵通る
        have : a ≠ 0 := ha_ne
        -- `simp` はデフォで `inv_mul_cancel` 系を使ってくれる
        simp [this]  -- a⁻¹ * a = 1

      -- まとめて 1 に落とす
      simp [hscale', hmul]


    have h_pivot_col_other_rows_zero :
      ∀ i' : Fin m,
        i' ≠ ⟨st.rowCount, h_row_lt_m⟩ →
        (matOf R₃) i' ⟨st.colPtr, hcol⟩ = 0 := by
      -- 補題の形に合わせて書き換え
      intro i' hi'
      have h :=
        clearPivotCol_pivot_col_other_rows_zero
          (R := R₂)
          (row := st.rowCount)
          (col := st.colPtr)
          (hrow := h_row_lt_m)
          (hcol := hcol)
          (hpiv := h_unit_piv_R₂)
      -- h : let R₃' := clearPivotCol R₂ ...; ∀ i' ≠ ..., matOf R₃' i' col = 0
      -- このファイル内の R₃ = clearPivotCol R₂ ... なので simp で一致させる
      have : (matOf (clearPivotCol R₂ st.rowCount st.colPtr hcol))
              i' ⟨st.colPtr, hcol⟩ = 0 :=
        h i' hi'
      simpa [R₃] using this

    have old_or_new (i : Fin new_r) :
      (i.val < st.rowCount) ∨ (i = Fin.last st.rowCount) := by
      by_cases hlt : i.val < st.rowCount
      · left; exact hlt
      · right
        unfold Fin.last
        have : i.val = st.rowCount := by
          -- i.val < st.rowCount.succ かつ ¬(i.val < st.rowCount) なので等しい
          have hi_lt_succ : i.val < st.rowCount + 1 := i.is_lt
          exact Nat.eq_of_lt_succ_of_not_lt hi_lt_succ hlt
        apply Fin.ext
        exact this

      -- I2_unit, I3_left0 は「旧行」の場合はそのまま継承
    have h_I2_old :
      ∀ i : Fin new_r, i.val < st.rowCount →
        (matOf R₃) (Fin.castLE h_bound_R₃.1 i)
          (extendPivot st.pivot ⟨st.colPtr, hcol⟩ i) = 1 ∧
        ∀ i' : Fin m,
          i' ≠ Fin.castLE h_bound_R₃.1 i →
          (matOf R₃) i'
            (extendPivot st.pivot ⟨st.colPtr, hcol⟩ i) = 0 := by
      intro i hi_lt
      have hi_lt' : (i.val : ℕ) < st.rowCount := hi_lt
      -- i を Fin st.rowCount に落とす
      let i_old : Fin st.rowCount := ⟨i, hi_lt'⟩

      -- extendPivot の旧部分は st.pivot i_old に一致
      have h_ext_eq :
        extendPivot st.pivot ⟨st.colPtr, hcol⟩ i =
          st.pivot i_old := by
        have := extendPivot_old (p := st.pivot)
          (newCol := ⟨st.colPtr, hcol⟩) (i := i) (hi := hi_lt')
        simpa [i_old] using this

      -- 元の Inv から unit ベクトル性
      have h_main := h_unit_R₂ i_old
      rcases h_main with ⟨h_one_R₂, h_zero_R₂⟩

      -- castLE での行 index の対応
      have h_cast :
        Fin.castLE h_bound_R₃.1 i =
          Fin.castLE h_bound_R₂.1 i_old := by
        apply Fin.ext
        -- どちらも値は i.val
        simp [Fin.castLE, new_r, i_old]

      ----------------------------------------------------------------
      -- ここから、旧 pivot 列 st.pivot i_old が R₂ と R₃ で一致していることを示す
      ----------------------------------------------------------------

      -- pivot 行 rowCount の旧 pivot 列成分が 0 である
      have h_pivot_zero :
        matOf R₂ ⟨st.rowCount, h_row_lt_m⟩ (st.pivot i_old) = 0 := by
        -- 旧 pivot 列は必ず colPtr より左なので newPivotRow_left_zero から出る
        have hj_lt_col :
          (st.pivot i_old : ℕ) < st.colPtr := h_in_R₂ i_old
        -- ここで使う lemma は手元の newPivotRow_left_zero の形に合わせて修正してね
        have h0 :=
          newPivotRow_left_zero
            (st := st) (i0 := i0)
            (hcol := hcol) (hsome := hsome)
            (R₂ := R₂) (hInv_R₂ := hInv_R₂')
            (j := st.pivot i_old) hj_lt_col
        simpa using h0

      -- 旧 pivot 列 (st.pivot i_old) は clearPivotCol 後も列ごと保存される
      have h_preserve_col :
        ∀ i' : Fin m,
          matOf R₃ i' (st.pivot i_old) =
            matOf R₂ i' (st.pivot i_old) := by
        -- R₃ = clearPivotCol R₂ st.rowCount st.colPtr hcol
        have := clearPivotCol_preserve_col
          (R := R₂) (row := st.rowCount) (col := st.colPtr)
          (hcol := hcol) (hrow := h_row_lt_m)
          (col' := st.pivot i_old)
          (h_pivot_zero := h_pivot_zero)
        -- 型がそのまま合う想定なら `exact` で、少し違えば `simpa [R₃] using ...`
        simpa [R₃] using this

      refine And.intro ?h_one ?h_zero
      · -- pivot = 1
        have h_eq_piv_row :
          (matOf R₃) (Fin.castLE h_bound_R₃.1 i) (st.pivot i_old) =
            (matOf R₂) (Fin.castLE h_bound_R₂.1 i_old) (st.pivot i_old) := by
          -- 列の保存 ＋ 行インデックスの一致を使う
          have hcol_eq :=
            h_preserve_col (Fin.castLE h_bound_R₃.1 i)
          -- hcol_eq :
          --   matOf R₃ (Fin.castLE h_bound_R₃.1 i) (st.pivot i_old)
          --   = matOf R₂ (Fin.castLE h_bound_R₃.1 i) (st.pivot i_old)
          simpa [h_cast] using hcol_eq

        -- h_one_R₂ :
        --   matOf R₂ (Fin.castLE h_bound_R₂.1 i_old) (st.pivot i_old) = 1
        -- を R₃ 側に引き戻す
        have h_one_R₂' := h_one_R₂
        -- 最後に書き換え
        have :
          (matOf R₃) (Fin.castLE h_bound_R₃.1 i)
            (extendPivot st.pivot ⟨st.colPtr, hcol⟩ i) = 1 := by
          -- extendPivot ... i = st.pivot i_old で列を書き換える
          simpa [h_ext_eq, h_eq_piv_row] using h_one_R₂'
        exact this
      · -- pivot 列の他の行は 0
        intro i' hi'_neq

        -- R₃ と R₂ で該当列の成分が一致
        have hcol_eq :
          matOf R₃ i' (st.pivot i_old) =
            matOf R₂ i' (st.pivot i_old) :=
          h_preserve_col i'

        -- h_zero_R₂ :
        --   ∀ i' : Fin m,
        --     i' ≠ Fin.castLE h_bound_R₂.1 i_old →
        --     matOf R₂ i' (st.pivot i_old) = 0
        have hi'_neq_R₂ :
          i' ≠ Fin.castLE h_bound_R₂.1 i_old := by
          -- Fin.castLE h_bound_R₃.1 i = Fin.castLE h_bound_R₂.1 i_old を使って
          -- 仮定 hi'_neq を書き換える
          intro h_eq
          apply hi'_neq
          -- hi'_neq : i' ≠ Fin.castLE h_bound_R₃.1 i
          -- h_eq : i' = Fin.castLE h_bound_R₂.1 i_old
          have : Fin.castLE h_bound_R₃.1 i =
            Fin.castLE h_bound_R₂.1 i_old := h_cast
          -- これで i' = Fin.castLE h_bound_R₃.1 i が従う
          simp [h_eq, this]

        have h_zero_R₂' :
          matOf R₂ i' (st.pivot i_old) = 0 :=
          h_zero_R₂ i' hi'_neq_R₂

        -- 0 を R₃ 側に引き戻す
        have :
          (matOf R₃) i'
            (extendPivot st.pivot ⟨st.colPtr, hcol⟩ i) = 0 := by
          -- 列を書き換えつつ hcol_eq, h_zero_R₂' を使う
          simpa [h_ext_eq, hcol_eq] using h_zero_R₂'
        exact this


      -- 新ピボット行用の I2_unit
    have h_I2_new :
      (matOf R₃) (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount))
        (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)) = 1 ∧
      ∀ i' : Fin m,
        i' ≠ Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount) →
        (matOf R₃) i'
          (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)) = 0 := by

      -- 新 pivot の列 index
      have h_ext_new :
        extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)
          = ⟨st.colPtr, hcol⟩ := by
        -- extendPivot の定義からの lemma
        -- （「last のときは新しい pivot 列を返す」）
        unfold extendPivot
        -- last の値は rowCount なので < rowCount は成り立たない
        simp

      -- 行 index の castLE を pivot 行にそろえる
      have h_cast_row :
        Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)
          = ⟨st.rowCount, h_row_lt_m⟩ := by
        apply Fin.ext
        simp [Fin.last, new_r]

      -- R₂ の方で pivot 行が unit ベクトルであること
      -- （行 st.rowCount に対する I2_unit）
      let i_piv : Fin (st.rowCount + 1) :=
        ⟨st.rowCount, by
          -- 0 ≤ rowCount < rowCount+1
          have : st.rowCount < st.rowCount + 1 := Nat.lt_succ_self _
          simp [this]⟩

      -- extendPivot の新側補題と合わせると、
      --   extendPivot ... i_piv = ⟨st.colPtr, hcol⟩
      -- みたいな形が使えるはず
      have h_ext_new_R₂ :
        extendPivot st.pivot ⟨st.colPtr, hcol⟩ i_piv
          = ⟨st.colPtr, hcol⟩ := by
        -- これも extendPivot_new 的な lemma にした方がきれい
        unfold extendPivot
        -- i_piv.val = st.rowCount なので < st.rowCount は成り立たない
        have : ¬ ((i_piv : Fin new_r).1 < st.rowCount) := by
          -- i_piv = ⟨st.rowCount, _⟩ なので val = st.rowCount
          dsimp [i_piv]
          exact Nat.lt_irrefl _
        simp [this]

      -- R₂ の Inv から unit ベクトル性
            -- R₂ の方で pivot 行の pivot 成分が 1 であること
      have h_unit_piv_R₂ :
        (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ = 1 := by
        have h :
          matOf R₂ ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ =
            a⁻¹ * matOf R₁ ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ := by
          -- R₂ = rScale R₁ st.rowCount a⁻¹
          simpa [R₂, a] using
            matOf_rScale_pivot (R := R₁)
              (row := st.rowCount) (hrow := h_row_lt_m)
              (k := a⁻¹) (j := ⟨st.colPtr, hcol⟩)

        have hR : matOf st.R i0 ⟨st.colPtr, hcol⟩ = a := by
          -- h_swap : matOf R₁ row col = matOf st.R i0 col
          -- a = matOf R₁ row col
          -- 向きを合わせるために symm を取って `a` に書き換える
          have := h_swap.symm
          -- ⊢ matOf st.R i0 col = a
          simpa [a] using this

          -- ← ここは環境に合わせて調整
        -- 右辺は a⁻¹ * a = 1
        have : a⁻¹ * a = (1 : K) := by
          -- ha_ne : a ≠ 0 を使って left_inv
          have ha_unit : IsUnit a := by
            -- Field K なので a ≠ 0 から unit を作れる（`isUnit_iff_ne_zero` 的な補題）
            simp [ha_ne]
          simp [a, ha_ne]
        simp [ h, h_swap, hR, this ]

      -- あとで使いやすいように別名にしておく
      let h_one_R₂ := h_unit_piv_R₂

      -- ここから R₂ → R₃ へ書き換えていく

      refine And.intro ?h1 ?h2
      · -- pivot 行・pivot 列 = 1
        have h_row_eq :
          matOf R₃ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) =
          matOf R₂ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) := by
          -- h_pivot_row_unchanged : matOf R₃ ⟨rowCount, _⟩ = matOf R₂ ⟨rowCount, _⟩
          -- を cast した形に直す
          simpa [h_cast_row] using h_pivot_row_unchanged

        -- その行ベクトルに対して、列インデックスを
        -- extendPivot ... last で評価したものを比較
        have h_row_eq_entry :
          (matOf R₃ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)))
              (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount))
          =
          (matOf R₂ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)))
              (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)) := by
          exact congrArg
            (fun (v : Fin n → K) =>
              v (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)))
            h_row_eq

        -- 行インデックス＆列インデックスを pivot 形に揃える
        have :
          (matOf R₃) (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount))
            (extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount))
          =
          (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ ⟨st.colPtr, hcol⟩ := by
          -- 行インデックスは h_cast_row、列は h_ext_new
          simpa [h_cast_row, h_ext_new] using h_row_eq_entry

        -- ここで h_one_R₂ : matOf R₂ (rowCount,colPtr) = 1 を流し込む
        have h_one_R₂ := h_unit_piv_R₂
        simpa [this] using h_one_R₂
      · -- pivot 列の他の行は 0
        intro i' hi'_neq
        -- TODO: ここはどういうロジック？？
        -- i' ≠ pivot 行（castLE 版）から i' ≠ ⟨rowCount, _⟩ を作る
        have hi'_neq_pivot :
          i' ≠ ⟨st.rowCount, h_row_lt_m⟩ := by
          intro h_eq
          -- h_cast_row :
          --   Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)
          --   = ⟨st.rowCount, h_row_lt_m⟩
          -- を使って hi'_neq と矛盾を作る
          apply hi'_neq
          -- i' = ⟨rowCount, _⟩ かつ castLE last = ⟨rowCount,_⟩ なので
          -- i' = castLE last になる
          have : Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)
                = ⟨st.rowCount, h_row_lt_m⟩ := h_cast_row
          -- `simpa [this] using h_eq` で i' = castLE last を得る
          simpa [this] using h_eq

        -- clearPivotCol の補題から R₃ で pivot 列が 0
        have h_zero_R₃ :
          (matOf R₃) i' ⟨st.colPtr, hcol⟩ = 0 :=
          h_pivot_col_other_rows_zero i' hi'_neq_pivot

        -- extendPivot の列 index に戻すだけ
        simpa [h_ext_new] using h_zero_R₃

    refine
    { I0_rows := ?_
    , I0_rect := ?_
    , I1_bound := ?_
    , I1_mono := ?_
    , I1_in := ?_
    , I2_unit := ?_
    , I3_left0 := ?_
    , I4_tail0 := ?_
    , I5_fac := ?_ }

    · -- I0_rows
      exact h_rows_R₃

    · -- I0_rect
      exact h_rect_R₃

    · -- I1_bound
      have hnewrow_le_m : st.rowCount + 1 ≤ m := by
        exact Nat.add_one_le_of_lt h_row_lt_m
      have hnewcol_le_n : st.colPtr + 1 ≤ n := by
        exact Nat.succ_le_of_lt hcol
      exact ⟨hnewrow_le_m, hnewcol_le_n⟩
    · -- I1_mono
      exact extendPivot_strictMono_state hcol

    · -- I1_in
      exact extendPivot_in hcol

    · -- I2_unit
      -- old/new 行に分けて上で書いた h_I2_old, h_I2_new を組合せ
      -- Fin (r+1) を「旧部分」と「新行」に分解する補助
      intro i
      have := old_or_new (i := i)
      cases this with
      | inl hi_lt =>
          exact h_I2_old i hi_lt
      | inr hi_last =>
          -- i = Fin.last の場合
          subst hi_last
          exact h_I2_new
    · -- I3_left0
      -- old/new 行に分けて同様に処理
      intro i j hj_lt
      have := old_or_new (i := i)
      cases this with
      | inl hi_lt =>
        -- 旧行の場合はそのまま継承
        let i_old : Fin st.rowCount := ⟨i, hi_lt⟩
        have h_ext_eq : extendPivot st.pivot ⟨st.colPtr, hcol⟩ i =
          st.pivot i_old := by
          -- extendPivot の定義に依存する補題を別途用意しておくと楽
          unfold extendPivot
          simp [hi_lt, i_old]
        -- j < extendPivot ... i を j < st.pivot i_old に書き換え
        have hj_lt' :
          (j : Nat) < (st.pivot i_old : Nat) := by
          simpa [h_ext_eq] using hj_lt

        -- 元の Inv (R₂, rowCount, colPtr, pivot) に対する I3_left0 を適用
        have h_zero_R₂ :
          (matOf R₂) (Fin.castLE h_bound_R₂.1 i_old) j = 0 :=
          h_left0_R₂ i_old j hj_lt'

        -- castLE h_bound_R₃.1 i と castLE h_bound_R₂.1 i_old の行インデックスは一致
        have h_cast :
          Fin.castLE h_bound_R₃.1 i =
            Fin.castLE h_bound_R₂.1 i_old := by
          apply Fin.ext
          simp [Fin.castLE, new_r, i_old]

        ----------------------------------------------------------------
        -- 列 j が R₂ と R₃ で一致していることを示す
        ----------------------------------------------------------------

        -- j < st.colPtr を作る（pivot(i_old) < colPtr なので）
        have hj_lt_col : (j : Nat) < st.colPtr := by
          exact lt_trans hj_lt' (h_in_R₂ i_old)

        -- 新 pivot 行 (rowCount 行) の列 j が R₂ で 0
        have h_pivot_zero :
          (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ j = 0 := by
          -- 「新 pivot 行の左側は 0」の補題を使う
          exact newPivotRow_left_zero
            (st := st) (i0 := i0)
            (hcol := hcol) (hsome := hsome)
            (R₂ := R₂) (hInv_R₂ := hInv_R₂') j hj_lt_col

        -- 「pivot 行のその列が 0 なので、その列は全行で clearPivotCol で保存される」
        have h_preserve_col :
          ∀ i' : Fin m,
            (matOf R₃) i' j = (matOf R₂) i' j := by
          -- clearPivotCol の定義を展開して列保存補題を使う
          -- R₃ = clearPivotCol R₂ st.rowCount st.colPtr hcol
          simpa [R₃] using
            clearPivotCol_preserve_col
              (R := R₂) (row := st.rowCount) (col := st.colPtr)
              (hcol := hcol) (hrow := h_row_lt_m)
              (col' := j)
              (h_pivot_zero := h_pivot_zero)

        -- 行ベクトル等式から j 成分の等式を取り出す
        have h_row_eq_j :
          (matOf R₃ (Fin.castLE h_bound_R₃.1 i) j) =
          (matOf R₂ (Fin.castLE h_bound_R₃.1 i) j) :=
            h_preserve_col (Fin.castLE h_bound_R₃.1 i)

        -- 旧側の 0 を R₃ に引き戻す
        calc
          matOf R₃ (Fin.castLE h_bound_R₃.1 i) j
              = matOf R₂ (Fin.castLE h_bound_R₃.1 i) j := h_row_eq_j
          _   = matOf R₂ (Fin.castLE h_bound_R₂.1 i_old) j := by
                  simp [h_cast]
          _   = 0 := h_zero_R₂
      | inr hi_last =>
        -- 新 pivot 行のケース
        subst hi_last

        -- extendPivot は last インデックスで新 pivot 列 colPtr を返す（要補題）
        have h_ext_new :
          extendPivot st.pivot ⟨st.colPtr, hcol⟩ (Fin.last st.rowCount)
            = ⟨st.colPtr, hcol⟩ := by
          -- extendPivot の定義から作る lemma
          unfold extendPivot
          simp [Fin.last]

        -- j < extendPivot ... last から j < colPtr を取り出す
        have hj_lt_col :
          (j : Nat) < st.colPtr := by
          simpa [h_ext_new] using hj_lt

        -- 「新 pivot 行の左側 0」補題を適用
        have h_zero_R₂ :
          (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ j = 0 :=
          newPivotRow_left_zero
            (st := st) (i0 := i0)
            (hcol := hcol) (hsome := hsome)
            (R₂ := R₂) (hInv_R₂ := hInv_R₂') j hj_lt_col

        -- castLE で使っているインデックスと ⟨rowCount, h_row_lt_m⟩ を同一視
        have h_cast :
          Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)
            = ⟨st.rowCount, h_row_lt_m⟩ := by
          apply Fin.ext
          simp [Fin.last, new_r]

        -- R₂ と R₃ で pivot 行は一致する
        have h_row_eq :
          matOf R₃ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) =
          matOf R₂ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) := by
          -- h_pivot_row_unchanged : matOf R₃ ⟨st.rowCount, h_row_lt_m⟩ = ...
          simpa [h_cast] using h_pivot_row_unchanged

        -- そこから j 成分を取り出す
        have h_row_eq_j :
          matOf R₃ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) j =
          matOf R₂ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) j := by
          exact congrArg (fun (v : Fin n → K) => v j) h_row_eq

        -- 旧側の 0 を R₃ に引き戻す
        calc
          matOf R₃ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) j
              = matOf R₂ (Fin.castLE h_bound_R₃.1 (Fin.last st.rowCount)) j := h_row_eq_j
          _   = matOf R₂ ⟨st.rowCount, h_row_lt_m⟩ j := by
                  simp [h_cast]
          _   = 0 := h_zero_R₂

    -- I4_tail0
    · intro j hj_lt hj_not_pivot i' hi_ge
      -- j.val < colPtr + 1 から j.val ≤ colPtr をとる
      have hj_le_col : (j : ℕ) ≤ st.colPtr := by
        have := hj_lt
        -- new_c = st.colPtr + 1
        have : (j : ℕ) < st.colPtr + 1 := by simpa [new_c] using this
        exact Nat.lt_succ_iff.mp this

      -- j.val < colPtr か j.val = colPtr に分ける
      have hj_cases : (j : ℕ) < st.colPtr ∨ (j : ℕ) = st.colPtr :=
        lt_or_eq_of_le hj_le_col

      cases hj_cases with
      | inl hj_lt_col =>
        -- (1) 新しい仮定 (∀ i : Fin new_r, new_piv i ≠ j)
        --     から、旧 pivot に対しても st.pivot i ≠ j を取り出す
        have h_old_not_pivot :
          ∀ i0 : Fin st.rowCount, st.pivot i0 ≠ j := by
          intro i0
          -- i0 を Fin (rowCount+1) に埋め込んで extendPivot を使う
          -- ここは extendPivot の「旧部分」補題が必要：
          -- extendPivot_old :
          --   ∀ i0, extendPivot st.pivot ⟨st.colPtr, hcol⟩ (embed i0) = st.pivot i0
          have h_ext_old :
            extendPivot st.pivot
              ⟨st.colPtr, hcol⟩
              (Fin.castLE (n:= st.rowCount) (m:= st.rowCount + 1) (Nat.le_succ st.rowCount) i0) =
              st.pivot i0 := by
            -- extendPivot の定義から証明する（別 lemma として用意しておく）
            unfold extendPivot
            simp
          -- j が pivot ではない（新 Inv の仮定）
          have hnp :=
            hj_not_pivot
              (Fin.castLE (n:= st.rowCount) (m:= st.rowCount + 1) (Nat.le_succ st.rowCount) i0)
          -- simp で st.pivot i0 ≠ j を得る
          simpa [new_piv, h_ext_old] using hnp

        -- (2) 行下界: rowCount+1 ≤ i' ⇒ rowCount ≤ i'
        have hi_ge_old : st.rowCount ≤ (i' : ℕ) := by
          -- rowCount ≤ rowCount + 1 ≤ i'
          exact le_trans (Nat.le_succ _) hi_ge

        -- (3) 旧 Inv の I4_tail0 を適用
        have h_zero_R₂ :
          matOf R₂ i' j = 0 :=
          h_tail0_R₂ j hj_lt_col h_old_not_pivot i' hi_ge_old

        -- (4) R₂ → R₃ への書き換え
        --     「pivot 列より左の列は clearPivotCol で変わらない」補題を使う
        -- まず R₂ に対する "pivot 行の左側 0" を用意
        have h_pivot_left0_R₂ :
          ∀ j' : Fin n, (j' : ℕ) < st.colPtr →
            (matOf R₂) ⟨st.rowCount, h_row_lt_m⟩ j' = 0 :=
          fun j' hj' =>
            newPivotRow_left_zero
              (st := st) (i0 := i0)
              (hcol := hcol) (hsome := hsome)
              (R₂ := R₂) (hInv_R₂ := hInv_R₂')
              j' hj'

        -- 次に clearPivotCol_preserves_left_cols を適用して
        -- matOf R₃ i' j = matOf R₂ i' j を得る
        have h_preserve :
          (matOf R₃) i' j = (matOf R₂) i' j := by
          -- R₃ = clearPivotCol R₂ ...
          have h :=
            clearPivotCol_preserves_left_cols
              (R := R₂)
              (row := st.rowCount)
              (col := st.colPtr)
              (hcol := hcol)
              (h_row_lt_m := h_row_lt_m)
              (h_pivot_left0 := h_pivot_left0_R₂)
              i' j hj_lt_col
          simpa [R₃] using h

        -- 旧側の 0 を R₃ に持ってくる
        have h_zero_R₃ : (matOf R₃) i' j = 0 := by
          simpa [h_preserve] using h_zero_R₂

        exact h_zero_R₃

      | inr hj_eq_col =>
        -- (1) j = colPtr なので、Fin の同値も作る
        have hj_eq :
          j = ⟨st.colPtr, hcol⟩ := by
          apply Fin.ext
          -- 値が等しいことを示せば OK
          -- hj_eq_col : (j : ℕ) = st.colPtr
          simp [hj_eq_col]  -- 右辺は st.colPtr

        -- (2) new_piv の last で矛盾を作る
        let i_last : Fin new_r := Fin.last st.rowCount

        have h_new_piv_last :
          new_piv i_last = ⟨st.colPtr, hcol⟩ := by
          -- i_last = Fin.last st.rowCount なので、その val は st.rowCount
          have h_not_lt :
            ¬ ((i_last : Fin new_r).1 < st.rowCount) := by
            -- new_r = st.rowCount + 1 なので、i_last を dsimp すると
            -- i_last.val = st.rowCount になるはず
            dsimp [i_last, new_r]  -- i_last = Fin.last st.rowCount を展開
            -- ここでゴールは ¬ (st.rowCount < st.rowCount)
            exact (Nat.lt_irrefl _)

          -- extendPivot を展開して、if の条件に h_not_lt を適用
          unfold new_piv extendPivot
          -- 条件が「偽」であることを教えて、else ブランチ（新 pivot）に落とす
          have : ¬ ((i_last : Fin new_r).1 < st.rowCount) := h_not_lt
          simp [this]      -- これでゴールが refl に落ちるはず

        have h_false : False := by
          have hnp := hj_not_pivot i_last
          -- new_piv i_last = j であることを使って矛盾
          have : new_piv i_last = j := by
            simpa [hj_eq] using h_new_piv_last
          -- hnp : new_piv i_last ≠ j なので矛盾
          exact hnp this

        -- (3) False からは何でも示せるので目標は自明
        exact (False.elim h_false)

    · -- I5_fac
      exact h_fac_R₃

  -- R₃ = R₂ なので just rewrite
  exact hInv_step


-- ==============================
-- 1ステップ関数
-- ==============================

@[inline] def μ {m n K} [Field K] (st : GEStateP m n K) : Nat := n - st.colPtr

def μ_exec {m n K} [Field K] (st : GEExecState m n K) : Nat := n - st.colPtr

@[simp] lemma μ_exec_erase {m n K} [Field K] (st : GEStateP m n K) :
  μ_exec (erase st) = μ st := by
  simp [μ, μ_exec, erase]

-- 1 ステップ進める関数（証明版）
noncomputable def geStepP
  {m n K} [Field K]
  (st : GEStateP m n K) (hcol : st.colPtr < n) : GEStateP m n K :=
  match hsearch : findPivot_spec st hcol with
  | none =>
      let new_c := st.colPtr + 1
      have inv' : Inv st.M0 st.R st.rowCount new_c st.pivot :=
        inv_step_none hcol hsearch
      {
        M0 := st.M0,
        R := st.R,
        rowCount := st.rowCount,
        colPtr := new_c,
        pivot := st.pivot,
        inv := inv'
      }
  | some i0 =>
      let R₁ := rSwap st.R st.rowCount i0.val
      let a  := (matOf R₁) ⟨st.rowCount, _⟩ ⟨st.colPtr, _⟩
      let R₂ := rScale R₁ st.rowCount (a⁻¹)
      let R₃ := clearPivotCol R₂ st.rowCount st.colPtr hcol
      let new_r   := st.rowCount + 1
      let new_c   := st.colPtr + 1
      let new_piv := extendPivot st.pivot ⟨st.colPtr, _⟩
      have inv' : Inv st.M0 R₃ new_r new_c new_piv := inv_step_some hcol hsearch
      { M0 := st.M0, R := R₃, rowCount := new_r, colPtr := new_c, pivot := new_piv, inv := inv' }

------------------------------------------------------------------
-- 補助関数: ピボットマップの拡張 (geStepP の extendPivot に相当)
------------------------------------------------------------------
/- 既存の写像 f : Fin n → α に、新しい値 a : α を末尾に追加して Fin (n+1) → α を作る -/
def extendPivot_exec
  {k : Nat} {α : Type u}
  (f : Fin k → α) (a : α) : Fin (k + 1) → α :=
  Fin.snoc f a

------------------------------------------------------------------
-- 実装: stepKernel
------------------------------------------------------------------

/-
  Gaussian Elimination の 1 ステップ（実行版）。
  geStepP と完全に構造を一致させており、erase との可換性が示しやすいようになっています。
-/
def stepKernel
  {m n K} [Field K] [DecidableEq K]
  (st : GEExecState m n K) : GEExecState m n K :=
  if h : st.rowCount < m ∧ st.colPtr < n then
    -- 証明版の findPivot_spec に対応する実行版 findPivot_exec を呼ぶ
    match findPivot_exec st h.2 with
    | none =>
        -- Pivot が見つからなかった場合: colPtr だけ進める
        { st with
          colPtr := st.colPtr + 1
        }
    | some i0 =>
        -- Pivot が見つかった場合 (i0 は Fin m)
        let r := st.rowCount
        let c := st.colPtr

        -- 1. Swap: 行 r と 行 i0 を入れ替え
        let R₁ := rSwap st.R r i0

        -- 2. Scale: 行 r の先頭係数 a を取得して正規化
        --    実行用なので Fin の証明は h から生成
        let fi : Fin m := ⟨r, h.1⟩
        let fj : Fin n := ⟨c, h.2⟩
        let a  := (matOf R₁) fi fj
        let R₂ := rScale R₁ r (a⁻¹)

        -- 3. Eliminate: 他の行を掃き出し (clearPivotCol は実行可能関数と想定)
        let R₃ := clearPivotCol R₂ r c h.2

        -- 4. Update State: カウンタとピボット情報を更新
        let new_r   := r + 1
        let new_c   := c + 1
        let new_piv := extendPivot st.piv fj

        { M0 := st.M0
        , R := R₃
        , rowCount := new_r
        , colPtr := new_c
        , piv := new_piv
        }
  else
    -- 停止条件を満たしている場合は何もしない
    st
-- TODO: 1 ステップの関数を実装する。証明と実行用を分けて後でつなぐ。

/- -/
lemma stepP_erases_to_kernel
  {m n K} [Field K] (stP : GEStateP m n K) (hcol : stP.colPtr < n) :
  erase (geStepP stP hcol) = stepKernel (erase stP) :=
by
  classical
  -- doneP stP / ¬doneP stP で分けるか、
  -- geStepP 側には doneP ガードがないなら pivot 分岐だけを見るか、設計次第
  have hdoneP_or := (doneP_iff_rEqm_or_cEqn (st := stP))
  -- 通常は geRunWF_P 内で ¬ doneP stP のときだけ geStepP を呼ぶので
  -- lemma を「¬ doneP stP を仮定して…」の形で書いても OK
  -- ここでは pivot の分岐に注目：
  cases hspec : findPivot_spec stP hcol with
  | none =>
      have hExec : findPivot_exec (erase stP) hcol = none := by
        -- findPivot_spec_vs_exec から
        sorry
      -- now simp both sides
      simp [geStepP, stepKernel, hspec, hExec, erase]  -- record equality になる
  | some i0 =>
      have hExec : findPivot_exec (erase stP) hcol = some i0 := by
        -- 同じく対応 lemma から
        sorry
      simp [geStepP, stepKernel, hspec, hExec, erase]
      -- rSwap / rScale / extendPivot などが両側で同じ式になっているので
      -- record 各フィールドごとに refl で潰れる


/- pivot が見つかった場合、その i0 行が確かに非零 -/
lemma findPivot_spec_some_sound_new
  {m n K} [Field K]
  {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (h : findPivot_spec st hcol = some i0) :
  (st.rowCount : Nat) ≤ i0 ∧
  (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 := by
  classical
  -- findPivot_spec の定義で使う命題
  let Hex : Prop := ∃ r : Nat, PivotIndexPred st hcol r

  -- Hex が偽だと findPivot_spec = none となり、仮定 h と矛盾するので Hex は真
  have hHex : Hex := by
    by_contra hFalse
    have hnone : findPivot_spec st hcol = none := by
      unfold findPivot_spec
      simp [Hex, hFalse]
    -- h : findPivot_spec st hcol = some i0 と矛盾
    exact Option.noConfusion (Eq.trans h.symm hnone)

  -- h から「実際に返しているのは Classical.choose hP」であることを引き出す
  have h' := h
  unfold findPivot_spec at h'
  -- Hex は真なので if_pos、右辺は some (Classical.choose hP) に簡約
  -- ここで hP := Nat.find_spec hHex とおく
  have hP : PivotIndexPred st hcol (Nat.find hHex) :=
    Nat.find_spec hHex
  have h'' :
    some (Classical.choose hP) = some i0 := by
    -- definitional equality で Nat.find_spec hHex = hP と見なせる
    simpa [Hex, hHex, hP] using h'

  -- some の injectivity から、中身が等しい
  have hi0 :
    Classical.choose hP = i0 :=
    Option.some.inj h''

  -- hP から Classical.choose hP に対する性質（rowCount 以上 & 非零）を取り出す
  have hP_spec :
    (st.rowCount : Nat) ≤ Classical.choose hP ∧
    (matOf st.R) (Classical.choose hP) ⟨st.colPtr, hcol⟩ ≠ 0 :=
  by
    -- PivotIndexPred の中身：∃ i, i.val = ... ∧ rowCount ≤ ... ∧ ...
    rcases Classical.choose_spec hP with
      ⟨h_val_eq, h_ge, h_nz⟩
    -- 行番号の等しさ h_val_eq はここでは使わないので捨てて OK
    conv at h_ge =>
      rhs
      rw [← h_val_eq]
    exact ⟨h_ge, h_nz⟩

  -- これを i0 についての主張に書き換える
  have hP_spec_i0 :
    (st.rowCount : Nat) ≤ i0 ∧
    (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 :=
    by
      rw [hi0] at hP_spec
      exact hP_spec

  exact hP_spec_i0


-- doneExecP なら stepKernel は恒等変換
lemma stepKernel_doneExecP_id
  {m n K} [Field K] {st : GEExecState m n K}
  (h : doneExecP st) :
  stepKernel st = st := by
  -- doneExecP の展開
  unfold doneExecP at h
  -- stepKernel の展開
  unfold stepKernel
  -- h : ¬ (st.rowCount < m ∧ st.colPtr < n)
  -- なので if 条件は偽、`else st` ブランチになる
  simp [h]

-- 1. 1ステップで M0 は書き換えない（レコード更新が M0 に触れない）
lemma geStepP_preserves_M0
  {m n K} [Field K] (s : GEStateP m n K) (hcol : s.colPtr < n) :
  (geStepP s hcol).M0 = s.M0 := by
  -- geStepP の定義を展開して record 更新部分を見る
  unfold geStepP
  -- どちらの分岐でも M0 はそのまま
  cases h : findPivot_spec s hcol with
  | none =>
      simp
  | some i0 =>
      simp

-- 2. doneP でなければ colPtr < n
lemma colPtr_lt_n_of_not_done
  {m n K} [Field K] {s : GEStateP m n K}
  (h : ¬ doneP s) : s.colPtr < n := by
  classical
  by_contra hcn
  have hdone : doneP s := by
    dsimp [doneP]
    intro h'
    exact hcn h'.2
  exact h hdone

-- 3. 1ステップで μ が厳密に減少する
lemma geStepP_decreases_of_lt {m n K} [Field K]
  (s : GEStateP m n K) (hcn : s.colPtr < n) :
  μ (geStepP s hcn) < μ s := by
  cases h : findPivot_spec s hcn with
  | none =>
      -- 目標: n - (s.colPtr + 1) < n - s.colPtr
      simp [μ, geStepP, h]
      exact Nat.sub_lt_sub_left hcn (Nat.lt_succ_self s.colPtr)
  | some _ =>
      simp [μ, geStepP, h]
      exact Nat.sub_lt_sub_left hcn (Nat.lt_succ_self s.colPtr)

-- ==============================
-- メインループ (well-founded)
-- ==============================

noncomputable def geRunWF_P {m n K} [Field K] : GEStateP m n K → GEStateP m n K
| st =>
  by
    by_cases h : doneP st
    · exact st
    · exact geRunWF_P (geStepP st (colPtr_lt_n_of_not_done (s:=st) h))
termination_by st => μ st
decreasing_by
  have hcn : st.colPtr < n := colPtr_lt_n_of_not_done (s:=st) h
    -- strict decrease を適用
  have : μ (geStepP st hcn) < μ st := geStepP_decreases_of_lt (s:=st) hcn
  simpa [geRunWF_P, h] using this

def geRunExec {m n K} [Field K] (fuel : Nat) (st : GEExecState m n K) : GEExecState m n K :=
  -- fuel 回 stepKernel を回す単純ループ（while相当）
  Nat.iterate stepKernel fuel st


-- fuel が十分大きければ結果は変わらない、を示す補題
lemma reach_final_with_enough_fuel
  {m n K} [Field K]
  (st0 : GEExecState m n K)
  (fuel fuel' : Nat)
  (hge : fuel ≥ fuel')
  (hstop : doneExecP (geRunExec fuel' st0)) :
  geRunExec fuel st0 = geRunExec fuel' st0 := by
  unfold geRunExec at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
    -- fuel' 回後の状態を s' とおく
  set s' := Nat.iterate stepKernel fuel' st0 with hs'
  have hstop' : doneExecP s' := by
    -- hstop : doneExecP (geRunExec fuel' st0) から
    simpa [geRunExec, hs'] using hstop
  have h_id : stepKernel s' = s' :=
    stepKernel_doneExecP_id hstop'
  -- s' からスタートして d 回回しても s' のまま、という補題
  have hconst : Nat.iterate stepKernel d s' = s' := by
    induction d with
    | zero =>
        -- 0 回なら当然 s'
        simp
    | succ d ih =>
        -- (d+1) 回 = 1 回回してから d 回
        -- 1 回回したら h_id で s' に戻るので、
        -- その後 d 回回しても ih で s'
        simp [Nat.iterate, h_id, ih]
  calc
    Nat.iterate stepKernel (fuel' + d) st0
      = Nat.iterate stepKernel d s' := by
        simp [s']
        conv =>
          rhs
          rw [<-Function.iterate_add_apply, Nat.add_comm]
      _ = s' := hconst
      _ = geRunExec fuel' st0 := by
        simp [geRunExec, hs']



-- 証明付きで実行した結果を消去しても、証明なしで実行した結果と一致する、を示す補題
lemma run_erases_to_exec
  {m n K} [Field K] (st : GEStateP m n K) :
  ∃ fuel ≤ μ_exec (erase st),
    erase (geRunWF_P st) = geRunExec fuel (erase st) :=
by
  -- WF再帰の帰納法＋ stepP_erases_to_kernel を使って、
  -- 各ステップで erase が一致すること（bisim）を示す。
  have hmain :
    ∀ k (st : GEStateP m n K),
      μ st ≤ k →
      ∃ fuel ≤ μ st,
        erase (geRunWF_P st) = geRunExec fuel (erase st) := by
        refine Nat.rec ?base ?step
        · -- base: k = 0 のとき
          intro st hk
          have hdone : doneP st := by
            by_contra hnd
            have hμ_pos : 0 < μ st := by
              have hcn : st.colPtr < n := colPtr_lt_n_of_not_done (s:=st) hnd
              simp [μ]
              exact hcn
            exact Nat.not_le_of_lt hμ_pos hk
          have : geRunWF_P st = st := by
            simp [geRunWF_P, hdone]
          refine ⟨0, ?fuel_le, ?eq⟩
          · simp
          · conv =>
              lhs
              rw [this]
            simp [geRunExec]
        · -- step: k → k+1 のとき
          intro k ih st hμ
          by_cases hdone : doneP st
          · have : geRunWF_P st = st := by
              simp [geRunWF_P, hdone]
            refine ⟨0, ?_, ?_⟩
            · exact Nat.zero_le _
            · conv =>
                lhs
                rw [this]
              simp [geRunExec]
          · -- まだ done でないので、1 ステップ進める
            have hcn : st.colPtr < n := colPtr_lt_n_of_not_done (s:=st) hdone
            have hμ_decr : μ (geStepP st hcn) < μ st := geStepP_decreases_of_lt (s:=st) hcn
            -- μ (geStepP st) ≤ k を作る
            have hμ_st' : μ (geStepP st hcn) ≤ k := by
              have : μ (geStepP st hcn) ≤ k := by
                have : μ (geStepP st hcn) < k.succ := Nat.lt_of_lt_of_le hμ_decr hμ
                exact Nat.le_of_lt_succ this
              exact this
            have hIH := ih (geStepP st hcn) ?hμ
            rcases hIH with ⟨fuel', hfuel'_le, heq⟩
            refine ⟨fuel' + 1, ?_, ?_⟩
            · -- fuel' + 1 ≤ μ st
              have h1 : fuel' < μ st := by
                exact
                  Nat.lt_of_le_of_lt hfuel'_le hμ_decr
              exact Nat.succ_le.mpr h1
            · -- erase (geRunWF_P st) = geRunExec (fuel' + 1) (erase st)
              have hWF :
                geRunWF_P st = geRunWF_P (geStepP st hcn) := by
                  rw [geRunWF_P]
                  simp [hdone]
              calc
                erase (geRunWF_P st)
                  = erase (geRunWF_P (geStepP st hcn)) := by rw [hWF]
                _ = geRunExec fuel' (erase (geStepP st hcn)) := heq
                _ = geRunExec fuel' (stepKernel (erase st)) := by
                  rw [stepP_erases_to_kernel]
                _ = geRunExec (fuel' + 1) (erase st) := by
                  simp [geRunExec, Nat.iterate]
            · -- μ (geStepP st) ≤ k を示す。
              exact hμ_st'
  -- 最後に hmain を st と μ st で適用
  obtain ⟨fuel, hfuel_le, heq⟩ := hmain (μ st) st (rfl.le)
  exact ⟨fuel, hfuel_le, heq⟩

/- Inv の I5 を使えば 元の行列の rank と最後の行列の rank が等しいことが geRun を使った場合でも示せるはず（geRun は Inv を保持するので）。-/
/- REF の rank はピボット本数に等しい -/
/- 1.ピボット列が一次独立（各ピボット列は標準基底ベクトルそのもの）
  2.任意の列はピボット列の線形結合で書ける（ピボット行の成分を係数にする）
  これによって列空間の次元 = ピボット列の数  = ref.r であることを示す。-/
lemma rank_of_REF_eq_pivot_count
  {m n K} [Field K] {A : Matrix (Fin m) (Fin n) K}
  {ref : REFMeta m n} (h : IsREF A ref) :
  Matrix.rank A = ref.r := by
  -- （行の埋め込み） pivot 行を Fin ref.r → Fin m に埋める
  let rowOf : Fin ref.r → Fin m := fun i => Fin.castLE (ref.hr) i

  obtain ⟨
    h_pivot_is_one,
    h_zero_row_or,
    h_other_rows_pivot_zero,
    h_left_zero,
    h_pivot_increasing
  ⟩ := h

  have hinj_rowOf : Function.Injective rowOf := by
    intro i j hij
    simp [rowOf] at hij
    exact hij

  -- === (a) ピボット列が一次独立 ===
  -- ピボット列は各 i について「rowOf i の位置だけ 1、他は 0」の列ベクトル
  have pivot_col_is_single :
    ∀ i : Fin ref.r, A.col (ref.pivot i) = Pi.single (rowOf i) (1 : K) := by
    intro i
    funext i'
    -- I2: ピボット列は縦に単位ベクトル（行 rowOf i で1、他は0）
    by_cases hrow : i' = rowOf i
    · conv =>
        rhs
        rw [<-hrow]
        simp [h_pivot_is_one i]
      simp [hrow, rowOf, h_pivot_is_one i]
    · simp [hrow]
      exact h_other_rows_pivot_zero (i:=i') (k:=i) hrow

  -- 標準基底は Linear Independent
  have hLIstd :
    LinearIndependent K (fun j : Fin m => Pi.single j (1 : K)) := by
    -- std basis on Pi はこれ
    simpa using Pi.linearIndependent_single_one (ι := Fin m) (R := K)

  -- 標準基底の線形独立性を使う
  -- （置換 + comp）でピボット列の Linear Independent を得る
  have linInd_pivots :
    LinearIndependent K (fun i : Fin ref.r => A.col (ref.pivot i)) := by
    -- まず「等しい族」へ差し替え
    have : (fun i : Fin ref.r => A.col (ref.pivot i))
        = (fun i : Fin ref.r => Pi.single (rowOf i) (1 : K)) := by
      funext i; simpa using pivot_col_is_single i
    -- `hLIstd` を `rowOf` で合成（comp）して LI を引き継ぐ
    --   hs.comp f hf : LinearIndependent R (v ∘ f)
    simpa [this] using hLIstd.comp rowOf hinj_rowOf


  -- === (b) 任意の列はピボット列の線形結合に入る（span 包含） ===
  -- 「列空間 ⊆ pivot 列の span」
  have all_cols_in_span :
    ∀ j : Fin n,
      A.col j ∈ Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) := by
    -- ある列 j について示す
    intro j
    -- 係数は「ピボット行の成分」
    let coeff : Fin ref.r → K := fun i => A (rowOf i) j
    -- 列ベクトルの等式：A.col j = Σ_i coeff i • A.col (ref.p i)
    have col_as_sum :
      A.col j = ∑ i : Fin ref.r, (coeff i) • A.col (ref.pivot i) := by
      funext i'
      -- 行 i' で評価
      -- case 分け：i' が pivot 領域(< ref.r)か、それ以外(≥ ref.r)か
      by_cases hi : (i' : Nat) < ref.r
      · -- i' < ref.r → ある k : Fin ref.r で rowOf k = i'
        let k : Fin ref.r := ⟨i', hi⟩
        have hk : rowOf k = i' := by
          simp [rowOf, k]
        -- 右辺の和を `pivot_col_is_single` で展開すると、k の項だけ (coeff k) が残る
        -- 係数 coeff k = A (rowOf k) j，列側は「rowOf k の位置だけ 1」
        -- よって和は A i' j に一致
        have : (∑ i : Fin ref.r, coeff i • (A.col (ref.pivot i))) i'
                = coeff k * 1 + (∑ i≠k, coeff i * 0) := by
          -- 実質 simp で潰れる
          simp [coeff, pivot_col_is_single, hk, Pi.single_apply]
          -- injectivity から (rowOf x = i') ↔ (x = k)
          have eq_iff : ∀ x, i' = rowOf x ↔ x = k := by
            intro x
            constructor
            · intro h
              have : rowOf x = rowOf k := Eq.trans h.symm hk.symm
              exact hinj_rowOf this
            · intro h; rw [h, hk]
          -- これで if 条件を (x = k) に置き換え
          have : (∑ x, if i' = rowOf x then A (rowOf x) j else 0)
                  = ∑ x, if x = k then A (rowOf x) j else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            simp [eq_iff x]
          simp [this, hk]
        simp [this, coeff, Matrix.col_apply, hk]      -- LHS=RHS
      · -- i' ≥ ref.r のとき、右辺は各ピボット列がその行で 0 なので全体 0。
        have hge : (ref.r : Nat) ≤ i' := Nat.le_of_not_lt hi
        have rhs0 :
          (∑ i : Fin ref.r, coeff i • (A.col (ref.pivot i))) i' = 0 := by
          -- 各項 (A.col (ref.p i)) i' = 0 （ピボット列は pivot 行以外 0）
          have each0 : ∀ i, (A.col (ref.pivot i)) i' = 0 := by
            intro i
            have hi'r: i' ≥ ref.r := hge
            have hlt : i < ref.r := i.is_lt
            have hne : i' ≠ rowOf i := by
              have : i'.val > i.val := Nat.lt_of_lt_of_le hlt hi'r
              have : i'.val ≠ i.val := ne_of_gt this
              exact Fin.ne_of_val_ne this
            exact h_other_rows_pivot_zero (i:=i') (k:=i) hne
          have : (∑ i, coeff i • A.col (ref.pivot i)) i'
            = ∑ i, coeff i • (A.col (ref.pivot i) i') := by
            simp [Finset.sum_apply, Pi.smul_apply]
          -- 列ベクトル経由のゼロ主張を、成分表示に直す
          have h' : ∀ i, A i' (ref.pivot i) = 0 := by
            intro i
            -- each0 i : (A.col (ref.pivot i)) i' = 0
            simpa [Matrix.col_apply] using each0 i
          simp [this, h']
        -- 左辺 A i' j も 0 を示す必要あり
        --   pivot 列なら I2 から 0、非ピボット列なら I4 から下が 0
        have lhs0 : A i' j = 0 := by
          -- 分岐：j が pivot 列かどうか
          by_cases hp : ∃ t, ref.pivot t = j
          · -- pivot 列：I2 で「行 rowOf t 以外は 0」
            rcases hp with ⟨t, rfl⟩
            have hi'r: i' ≥ ref.r := hge
            have hlt : t < ref.r := t.is_lt
            have hne : i' ≠ rowOf t := by
              have : i'.val > t.val := Nat.lt_of_lt_of_le hlt hi'r
              have : i'.val ≠ t.val := ne_of_gt this
              exact Fin.ne_of_val_ne this
            exact h_other_rows_pivot_zero (i:=i') (k:=t) hne
          · -- 非ピボット列：I4（下側 0）を使う
            have not_pivot : ∀ i, ref.pivot i ≠ j := not_exists.mp hp
            exact Or.resolve_left (h_zero_row_or (i:=i') j) hi
        -- 以上で行 i' の等式が成り立つ
        simp [Matrix.col_apply, rhs0, lhs0]
    -- 上の等式から span への包含
    -- 「有限和」は span に入る：sum_mem/smul_mem を使う
    -- TODO: ここを理解したい。
    have : A.col j ∈ Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) := by
      -- `col_as_sum` を書き換えて、右辺を span に入れる
      refine col_as_sum ▸ ?_
      -- 省略名
      set P :
          Submodule K (Fin m → K) :=
        Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i)))

      -- 目標が  ∑ i : Fin ref.r, coeff i • A.col (ref.pivot i) ∈ P  という形になっている前提で：
      refine Submodule.sum_mem (p := P)
        (t := (Finset.univ : Finset (Fin ref.r))) ?_  -- ← s ではなく t
      -- 各項が P に入ることを示す
      intro i _hi
      have gen_in : A.col (ref.pivot i) ∈ P := Submodule.subset_span ⟨i, rfl⟩
      exact Submodule.smul_mem P (coeff i) gen_in


    exact this

  -- 列空間＝toLinearMap.range は「全列の span」と一致
  -- 片側：range ⊆ span(pivots)
  -- 行列 A : (m×n) が与えられているとして
  --  それを線形写像 A_lin : K^n → K^m に変換する
  let A_lin : (Fin n → K) →ₗ[K] (Fin m → K) := Matrix.mulVecLin A

  -- A_lin の像（列空間）は pivot 列の span に入る
  have range_le :
    LinearMap.range A_lin
      ≤ Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) := by
    -- range は列ベクトルの像の張る空間。基底 e_j を通した像が col j。
    -- よって各 col j が上の span に入る ⇒ range 全体が入る。
    intro y hy
    rcases hy with ⟨x, rfl⟩
    -- 元のベクトル空間は K^n
    -- Pi.single に型注釈をつけないといけない。
    have hx : x = ∑ j : Fin n, x j • (Pi.single j (1 : K) : Fin n → K) := by
      funext i
      simp [Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

    have hx' : A_lin x = ∑ j : Fin n, x j • A_lin (Pi.single j (1 : K) : Fin n → K) := by
      conv =>
        lhs
        rw [hx]
      simp [map_sum]


    have hcol : ∀ j : Fin n,
      A_lin (Pi.single j (1 : K) : Fin n → K) = A.col j := by
      intro j
      funext i'
      simp [A_lin]

    have hA_lin_x : A_lin x = ∑ j : Fin n, x j • A.col j := by
      rw [hx']
      congr
      funext j
      rw [hcol j]

    have :
    ∀ j : Fin n, x j • A.col j
      ∈ Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) := by
      intro j
      exact
      Submodule.smul_mem
        (Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))))
        (x j)
        (all_cols_in_span j)
    simp [hA_lin_x]
    refine Submodule.sum_mem
      (p := Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))))
      (t := (Finset.univ : Finset (Fin n)))
      ?_
    intro j _hj
    exact this j


  -- 逆側：pivot 列は range に入る（もちろん列だから）
  -- つまり span(pivots) ⊆ range
  have span_le_range :
    Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i)))
      ≤  LinearMap.range A_lin := by
    have hcol : ∀ j : Fin n,
      A_lin (Pi.single j (1 : K) : Fin n → K) = A.col j := by
      intro j
      funext i'
      simp [A_lin]
    refine Submodule.span_le.2 ?_
    intro y hy
    rcases hy with ⟨i, rfl⟩
    refine ⟨Pi.single (ref.pivot i) (1 : K), ?_⟩
    rw [hcol (ref.pivot i)]


  -- 次元（=rank）を挟み撃ち：range と span が相互包含だから同次元
  have eq_spaces :
    LinearMap.range A_lin
      = Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) :=
    le_antisymm range_le span_le_range

  -- 左辺の finrank が rank、右辺は「LI な ref.r 本の張る空間」だから次元 ref.r
  -- `linInd_pivots` から `finrank_span_eq_card` 系の補題を使う
  -- A_lin の像の次元 = pivot 列の本数
  have : Module.finrank K (LinearMap.range A_lin) = ref.r := by
    rw [eq_spaces]
    simp [finrank_span_eq_card linInd_pivots]
  -- rank の定義で仕上げ
  simpa [Matrix.rank] using this


-- 補題：左から単元行列をかけても rank は変わらない
lemma rank_mul_preserved_by_left_unit
  {m n K} [Field K] {E : Matrix (Fin m) (Fin m) K} {M : Matrix (Fin m) (Fin n) K}
  (hE : IsUnit E) :
  Matrix.rank (E * M) = Matrix.rank M
  := by
  have hdet : IsUnit (Matrix.det E) := (Matrix.isUnit_iff_isUnit_det (A := E)).mp hE
  exact rank_mul_eq_right_of_isUnit_det E M hdet


@[simp] lemma erase_rowCount {m n K} [Field K] (st : GEStateP m n K) :
  (erase st).rowCount = st.rowCount := rfl
@[simp] lemma erase_colPtr {m n K} [Field K] (st : GEStateP m n K) :
  (erase st).colPtr = st.colPtr := rfl
@[simp] lemma erase_R {m n K} [Field K] (s : GEStateP m n K) : (erase s).R  = s.R  := rfl
@[simp] lemma erase_M0 {m n K} [Field K] (s : GEStateP m n K) : (erase s).M0 = s.M0 := rfl
@[simp] lemma doneP_erase_eq {m n K} [Field K] (st : GEStateP m n K) :
  doneExecP (erase st) = doneP st := by
  unfold doneP doneExecP
  simp [erase_rowCount, erase_colPtr]


-- μ は既出: μ st := n - st.colPtr
lemma doneP_geRunWF_P {m n K} [Field K] :
  ∀ s : GEStateP m n K, doneP (geRunWF_P s)
:= by
  intro s
  let Rel := fun a b : GEStateP m n K => μ a < μ b
  have hwf : WellFounded Rel := InvImage.wf μ Nat.lt_wfRel.wf
  -- 良基 (well-founded) な帰納原理を μ に沿って取る
  have acc : Acc Rel s := (InvImage.wf μ Nat.lt_wfRel.wf).apply s
  -- acc で再帰
  -- revert s

  refine Acc.rec
    (motive := fun (s : GEStateP m n K) _ =>
      doneP (geRunWF_P (m:=m) (n:=n) (K:=K) s))
    ?step
    acc

  intro s _ ih
  unfold geRunWF_P
  by_cases h : doneP s
  · -- 停止分岐
    simp [h]
  · -- 継続分岐：1 ステップで μ が減るので IH を geStepP s に適用
    have hcn : s.colPtr < n := colPtr_lt_n_of_not_done (s:=s) h
    have hdec : μ (geStepP s hcn) < μ s := geStepP_decreases_of_lt s hcn
    have ih'  : doneP (geRunWF_P (geStepP s hcn)) := ih (geStepP s hcn) hdec
    simp [h]
    exact ih'


-- 実行版：WF版と fuel' で一致しているとき、行列等式に書き換え
lemma erase_final_mat_eq_exec
  {m n K} [Field K] {st : GEStateP m n K}
  {fuel' : Nat} {E : Matrix (Fin m) (Fin m) K}
  (hErase : erase (geRunWF_P st) = geRunExec fuel' (erase st))
  (hfac : matOf (geRunWF_P st).R = Matrix.mulᵣ E st.M0) :
  matOf (geRunExec fuel' (erase st)).R = Matrix.mulᵣ E st.M0 := by
  -- hErase で書き換えて simp
  simp [<-hErase, hfac]

-- =========================
-- メイン補題：M0 の不変性
-- =========================
lemma geRunWF_P_preserves_M0 {m n K} [Field K] :
  ∀ s : GEStateP m n K, (geRunWF_P s).M0 = s.M0 := by
  intro s0
  have wf : WellFounded (fun a b : GEStateP m n K => μ a < μ b) := (measure μ).wf
  refine wf.induction (C := fun s => (geRunWF_P s).M0 = s.M0) s0 ?step
  intro s ih
  by_cases hdone : doneP s
  · simp [geRunWF_P, hdone]
  · have hcn : s.colPtr < n := colPtr_lt_n_of_not_done (s:=s) hdone
    have hdec : μ (geStepP s hcn) < μ s := geStepP_decreases_of_lt s hcn
    have ih' := ih (geStepP s hcn) hdec
    rw [geRunWF_P]
    simp [hdone]
    rw [ih']
    exact geStepP_preserves_M0 s hcn

/- 〈最終形〉実行版 `geRunExec` の出力行列のランクは、入力行列 `M0` のランクと等しい。 -/
/- rectifiedOfMatrix さえ正しい挙動をするなら正当性が担保される。 -/
theorem geRunExec_rank_preserved
  {m n K} [Field K]
  (M0 : Matrix (Fin m) (Fin n) K)
  (fuel : Nat) (hfuel : fuel ≥ n) :
  let R0   : Rectified m n K := rectifiedOfMatrix M0
  let st0E : GEExecState m n K :=
    { M0 := M0, R := R0, rowCount := 0, colPtr := 0, piv := (Fin.elim0) }
  let outE := geRunExec fuel st0E
  Matrix.rank (matOf outE.R) = Matrix.rank M0 :=
by
  intro R0 st0E outE
  classical
  -- 証明版の初期状態
  have h0   : matOf R0 = M0 := matOf_rectifiedOfMatrix (K:=K) M0
  let st0P : GEStateP m n K :=
    { M0 := M0, R := R0, rowCount := 0, colPtr := 0, pivot := (Fin.elim0)
    , inv := inv_init M0 R0 h0 }

  -- bisim：WF版の最終状態と実行版 fuel' ステップが一致
  obtain ⟨fuel', hfuel'le, hErase⟩ := run_erases_to_exec (st := st0P)

  -- WF版の最終形：左から可逆 E を掛けた形（Inv.I5）
  rcases (geRunWF_P st0P).inv.I5_fac with ⟨E, hEunit, hfac⟩

  have hfac' : matOf (geRunWF_P st0P).R = Matrix.mulᵣ E st0P.M0 := by
    simp [hfac, geRunWF_P_preserves_M0]

    -- 実行版 fuel' の最終行列へ書換
  have hfinal' :
    matOf (geRunExec fuel' (erase st0P)).R = Matrix.mulᵣ E (erase st0P).M0 :=
    erase_final_mat_eq_exec (st := st0P) (fuel' := fuel') (E := E) hErase hfac'


  -- ランクは左可逆で不変
  have hrank' :
  Matrix.rank (matOf (geRunExec fuel' (erase st0P)).R) = Matrix.rank M0 :=
    by simpa [hfinal'] using rank_mul_preserved_by_left_unit (m:=m) (n:=n) (K:=K) hEunit

  -- fuel を任意の大燃料に戻す：十分大なら停止点以降は不変
  -- まず、fuel' で停止していること：
  have hdone' : doneExecP (geRunExec fuel' (erase st0P)) := by
    -- hErase と doneP の一致で示せる（WF版は停止点）
    have : doneP (geRunWF_P st0P) := by
      -- 定義上、WF版は doneP で停止している分岐で返る
      -- unfold しても良いが、ここは事実として扱ってOK（ループ終端）
      -- 必要なら、「μ=0 → doneP」補題を別途用意
      simp [doneP_geRunWF_P]
    -- 実行版へ転送

    rw [<-hErase]
    simp [doneP_erase_eq, this]


  have hreach :
      geRunExec fuel (erase st0P) = geRunExec fuel' (erase st0P) :=
    reach_final_with_enough_fuel (st0:=erase st0P) (fuel:=fuel) (fuel':=fuel')
      (hge := ge_trans hfuel (by exact hfuel'le)) -- fuel ≥ n ≥ fuel'
      (hstop := hdone')

  -- outE へ反映
  have : outE = geRunExec fuel' st0E := by
    -- st0E = erase st0P
    have : st0E = erase st0P := by
      simp [st0E, erase, R0, st0P]
    simp [outE, this, hreach]

  -- 最終結論
  simpa [this] using hrank'

/- TODO: ここまで示す -/
/-======================= ランク計算の実装（有限体版） =======================-/
/- 𝔽p 上の厳密ガウス消去ランク（完全消去・行入替あり） -/
def rankModP (A0 : Array (Array 𝔽p)) (m n : ℕ)
(hRowSize : A0.size = m) (hrect : Rect A0 n) : Nat :=
  Id.run do
    -- TODO: ここの設定がまずいかも
    let rows := m
    let cols := n
    have hrows : rows = m := by trivial
    have hcols : cols = n := by trivial
    let mut R : Rectified m n 𝔽p := ⟨A0, hRowSize, hrect⟩
    let mut r := 0
    let mut c := 0
    -- 補助
    let get (i j : Nat) (M : Array (Array 𝔽p)) : 𝔽p :=
      if h : i < M.size then
        let row := M[i]
        if h2 : j < row.size then row[j] else 0
      else 0

    while r < rows && c < cols do
      -- pivot 探索
      let mut piv : Option Nat := none
      for i in [r:rows] do
        if get i c R.A ≠ 0 then piv := some i; break
      match piv with
      | none     => c := c + 1
      | some i₀  =>
          -- 行入替
          R := rSwap R r i₀
          -- ピボット正規化
          let a := get r c R.A
          R := rScale R r (a⁻¹)
          for i in [0:rows] do
            if i ≠ r then
              let f := get i c R.A
              if f ≠ 0 then R := rAxpy R i r f
          r := r + 1
          c := c + 1
    return r

/- IO: ランダム点 α を s 個生成（`Vector (ZMod p) s`） -/
def samplePointVec (s : Nat) : IO (Vector 𝔽p s) :=
  match s with
  | 0 =>
      -- Vector のコンストラクタは Array を受け取るので #[] を使う
      pure ⟨#[], by simp⟩
  | Nat.succ s' => do
      let xs ← samplePointVec s'
      let x  ← IO.rand 0 (p - 1)       -- 0..p-1 の乱数
      let a  : 𝔽p := (x : ZMod p)      -- Nat → ZMod p のキャスト
      pure (xs.push a)                  -- Vector.push : Vector α n → α → Vector α (n+1)

def vecAsPoint {s} (xs : Vector 𝔽p s) : Fin s → 𝔽p := fun i => xs.get i

/- 1 試行：評価→rank -/
-- noncomputable def trialRank
--   {d m s : Nat}
--   (A : Matrix (Fin d) (Fin m) (MvPolynomial (Fin s) ℤ)) :
--   IO Nat := do
--   let xs ← samplePointVec (p := p) s
--   let α  := vecAsPoint xs
--   let Aeval := evalMatrixZMod (p := p) A α
--   let arr   := toArray2D Aeval
--   pure (rankModP (p := p) arr)

/-======================= 厳密フェーズ（分数体） =======================-/

/- フィールド K 上のガウス消去ランク（完全消去・行入替あり） -/

noncomputable def rankByGaussianElim
  {K} [Field K] (init : Array (Array K)) : Nat :=
  open Classical in
  Id.run do
    -- ★ これを最初に置く（この do ブロック内だけ有効なインスタンス）
    have _ : Inhabited K := ⟨(0 : K)⟩
    let rows := init.size
    let cols := if init.isEmpty then 0 else init[0]!.size
    let mut A := init
    let mut r := 0
    let mut c := 0
    let get (i j : Nat) (M : Array (Array K)) : K :=
      if i < M.size then
        let row := M[i]!
        if j < row.size then row[j]! else 0
      else 0
    let swapRows (i j : Nat) (M : Array (Array K)) :=
      if i < M.size ∧ j < M.size then
        let ri := M[i]!; let rj := M[j]!
        (M.set! i rj).set! j ri
      else M
    let rowScale (i : Nat) (k : K) (M : Array (Array K)) :=
      if i < M.size then
        let row := M[i]!
        let newRow := Id.run do
          let mut out := #[]
          for j in [0:row.size] do out := out.push (k * row[j]!)
          out
        M.set! i newRow
      else M
    let rowAxpy (i k : Nat) (α : K) (M : Array (Array K)) :=
      if i < M.size ∧ k < M.size then
        let ri := M[i]!; let rk := M[k]!
        let n := ri.size
        let newRow := Id.run do
          let mut out := #[]
          for j in [0:n] do out := out.push (ri[j]! - α * rk[j]!)
          out
        M.set! i newRow
      else M

    while r < rows && c < cols do
      let mut piv : Option Nat := none
      for i in [r:rows] do
        if get i c A ≠ 0 then piv := some i; break
      match piv with
      | none     => c := c + 1
      | some i₀  =>
          A := swapRows r i₀ A
          let a := get r c A
          A := rowScale r (a⁻¹) A
          for i in [0:rows] do
            if i ≠ r then
              let f := get i c A
              if f ≠ 0 then A := rowAxpy i r f A
          r := r + 1
          c := c + 1
    return r

/- 分数体上の厳密ランク（既存の `rankQ_compute` 相当） -/
noncomputable def rankQ_exact (P : Params) (G : Finset (Ground P)) : ℕ := by
  classical
  let K := FractionRing (MvPolynomial (Var P) ℚ)
  let d := d_col P
  let β := {e : Ground P // e ∈ G}
  let m := Fintype.card β
  let toβ : Fin m → β := (Fintype.equivFin β).symm
  let Mx : Matrix (Fin d) β K := restrictCols P G
  let init : Array (Array K) :=
    Array.ofFn (fun i : Fin d => Array.ofFn (fun j : Fin m => Mx i (toβ j)))
  exact rankByGaussianElim init

/-======================= ハイブリッド（乱択→厳密） =======================-/

/- あなたの構成行列（列は `G` に制限）を **ℚ-多項式**で返す（乱択用） -/
noncomputable def restrictColsPolyQ
  (P : Params) (G : Finset (Ground P)) :
  Matrix (Fin (d_col P)) {e : Ground P // e ∈ G} (MvPolynomial (Var P) ℚ) :=
  fun r c => (M_polyQ P) r c.1

-- 乱択フェーズ用：ℤ 係数の構成行列（列を G に制限）
noncomputable def restrictColsPolyZ
  (P : Params) (G : Finset (Ground P)) :
  Matrix (Fin (d_col P)) {e : Ground P // e ∈ G}
        (MvPolynomial (Var P) Int) :=
  fun r c => (M_polyZ P r c.1)    -- ← M_poly の定義式は係数が 0/1 なので ℤ でも同じ
                                 --    （MvPolynomial.X / + / * は係数環に多相）



/- 任意の変数集合 `σ`：`MvPolynomial σ Int` を `α : σ → ZMod p` で評価し，
    mod p の厳密ランク（ガウス消去）を返す。`RandRank.rankModP` は既存実装を想定。 -/
def trialRankVar
  {p : Nat} [Fact (Nat.Prime p)]
  {d m : Nat} {σ : Type*}
  (A : Matrix (Fin d) (Fin m) (MvPolynomial σ Int))
  (α : σ → ZMod p) : Nat :=
  let coeffHom := Int.castRingHom (ZMod p)
  let Aeval : Matrix (Fin d) (Fin m) (ZMod p) :=
    fun i j => MvPolynomial.eval₂Hom coeffHom α (A i j)
  let arr := Array.ofFn (fun i => Array.ofFn (fun j => Aeval i j))
  rankModP (p := p) arr

/- Var P → ZMod p の乱数関数を1つ作る（`←` は Unicode） -/
def mkAlphaIO (P : Params) (p : Nat) [Fact (Nat.Prime p)]
    : IO (Var P → ZMod p) := do
  -- 行ごとに長さ t の列ベクトルを乱数で用意
  let rowsList ← (List.range P.n).mapM (fun _ => do
    (List.range P.t).mapM (fun _ => do
      let x ← IO.rand 0 (p - 1)
      pure (x : ZMod p)))
  -- Array にしてから安全アクセス .get! を段階的に使う
  let tab : Array (Array (ZMod p)) := (rowsList.map (·.toArray)).toArray
  pure (fun ia => (tab[ia.1.val]!)[ia.2.val]!)

/- 純関数版：評価点列を外から与える（Var P 版）。 -/
noncomputable def rankQ_hybrid_withVar
  (P : Params) (G : Finset (Ground P))
  {p : Nat} [Fact (Nat.Prime p)]
  (alphas : List (Var P → ZMod p)) : Nat :=
by
  classical
  let d    := d_col P
  let m    := Fintype.card {e : Ground P // e ∈ G}
  let full := Nat.min d m
  -- ℤ 係数の多項式行列（列制限）
  let toFin : Fin m → {e : Ground P // e ∈ G} := (Fintype.equivFin _).symm
  let MpolyZ : Matrix (Fin d) (Fin m) (MvPolynomial (Var P) Int) :=
    fun i j => (restrictColsPolyZ P G) i (toFin j)
  -- 1 回の試行（mod p で厳密ランク）
  let trial : (Var P → ZMod p) → Nat :=
    fun α => trialRankVar (p := p) (A := MpolyZ) α
  -- T 回の最大値
  let best := alphas.foldl (fun acc α => Nat.max acc (trial α)) 0
  -- ★ タクティックを使わず、項で完結させる
  exact if h : best = full then full else rankQ_exact P G


/- IO 版：α を trials 個作って純関数版へ。 -/
noncomputable def rankQ_hybrid_IO
  (P : Params) (G : Finset (Ground P))
  (p : Nat) [Fact (Nat.Prime p)]
  (trials : Nat := 2) : IO Nat := do
  let alphas ← (List.range trials).mapM (fun _ => mkAlphaIO P p)  -- mkAlphaIO : Var P → ZMod p
  pure (rankQ_hybrid_withVar P G (p := p) alphas)



/- 閉包（計算版；`S_t` の閉包。とりあえず仕様版に委譲しておく）。 -/
noncomputable def closureFinset (P : Params) (C : Finset (Ground P)) : Finset (Ground P) :=
  St.closure P C

/- C の「各要素を 1 本外せば独立」の証拠（占位；`Prop`）。 -/
structure IndCertBundle (P : Params) (C : Finset (Ground P)) : Prop where
  (all_independent : ∀ e ∈ C, True)   -- ← 後で `St.indep P (C.erase e)` などに差し替え

/- C の従属性の証拠（占位；`Prop`）。 -/
structure DepCert (P : Params) (C : Finset (Ground P)) : Prop where
  (nontrivial_relation : True)         -- ← 後で「非自明な線形関係」等に差し替え

/- 回路証明を `Type` のレコードに包む（`Option` に入れられるようにする）。 -/
structure CircuitCert (P : Params) (G : Finset (Ground P)) where
  C : Finset (Ground P)                  -- 見つけた回路候補
  subset : C ⊆ G                              -- C は G の部分
  ind    : IndCertBundle P C                  -- 極小性の証拠（占位；`Prop` フィールド）
  dep    : DepCert P C                        -- 従属性の証拠（占位；`Prop` フィールド)

/- 「G の列が独立か？」（rank = 列数 を判定） -/
noncomputable def allColsIndependentBool (P : Params) (G : Finset (Ground P)) : Bool := by
  classical exact decide (rankQ_exact P G = Fintype.card {e : Ground P // e ∈ G})

/- G の中からサーキットを 1 つ返す（見つからなければ none；骨格実装）。
  方針：独立なら none。従属なら |S|=1,2,… の順で従属な部分集合を探索し、
  最初に見つかった S を返す（最小サイズゆえ circuit）。 -/
noncomputable def findCircuit
  (P : Params) (G : Finset (Ground P)) : Option (Finset (Ground P)) := by
  classical
  -- まず G 全体が独立なら回路は存在しない
  if h : allColsIndependentBool P G = true then exact none else
  -- 「従属か？」のブール判定（ランクと列数の比較）
  let dep : Finset (Ground P) → Bool := fun S => decide (rankQ_exact P S < S.card)
  -- k = 1..G.card の順で、従属な |S|=k の部分集合を列挙して最初の要素を取る
  -- （最初に見つかる k が最小サイズ ⇒ その S は極小従属 = circuit）
  let candidates : List (Finset (Ground P)) :=
    (List.range G.card).foldr (fun k acc =>
      -- |S| = k+1 の部分集合を列挙して dep で絞る
      (((G.powerset).filter (fun S => S.card = k + 1)).filter (fun S => dep S)).toList ++ acc) []
  exact candidates.head?

noncomputable def certifyCircuit
  (P : Params) (G : Finset (Ground P)) :
  Option (CircuitCert P G) := by
  classical
  -- まず `findCircuit` の結果で分岐
  match findCircuit P G with
  | none =>
      exact none
  | some C =>
      -- ここで C ⊆ G を再チェック（Prop は decidable なので if が使える）
      if hsubset : C ⊆ G then
        -- 占位の証拠を詰めて返す
        let ind : IndCertBundle P C := ⟨by intro _ _; trivial⟩
        let dep : DepCert P C       := ⟨trivial⟩
        exact some { C := C, subset := hsubset, ind := ind, dep := dep }
      else
        -- （理屈上は起こらないはずだが）保守的に none を返す
        exact none

end Checker


namespace CheckerCorrectness
open St Checker

/- Array 型にしても Rect であることの証明 -/

lemma rect_toArray2D {m n K} (M : Matrix (Fin m) (Fin n) K) :
  Rect (toArray2D M) n := by
  intro i hi; simp [toArray2D]  -- 各行の size = n

lemma size_toArray2D_rows {m n α} (M : Matrix (Fin m) (Fin n) α) :
  (toArray2D M).size = m := by
  simp [toArray2D]

lemma of_to_id_rect {m n K} (M : Matrix (Fin m) (Fin n) K) :
  toMat (toArray2D M) m n (size_toArray2D_rows M) (rect_toArray2D M) = M := by
  ext i j; simp [toMat, toArray2D]

/- rank も一致する（本命の橋渡し補題） -/
lemma rank_of_to_eq {m n K} [Field K] [Inhabited K]
  (M : Matrix (Fin m) (Fin n) K) :
  Matrix.rank (toMat (toArray2D M) m n (size_toArray2D_rows M) (rect_toArray2D M))
    = Matrix.rank M := by
  rw [of_to_id_rect]

/- ------------------------- 1) 行基本変形＝可逆左乗 → rank 不変 ------------------------- -/
/- swap, scale, x_i + α x_j の正当性 -/
/- 行入替: Array 実装 swapRows は `Matrix.swap` の左乗に一致 -/
lemma rectA
  {m n α} [Field α] (M : Matrix (Fin m) (Fin n) α) :
  let A := toArray2D M
  Rect A n := rect_toArray2D M


lemma toMat_swapRows
  {m n α} [Field α]
  (M : Matrix (Fin m) (Fin n) α) (i j : ℕ) (hi : i < m) (hj : j < m) :
  let A := toArray2D M
  let A' := swapRows i j A
  have hrectA : Rect A n := rect_toArray2D M
  have hAA' : A'.size = A.size := by simp [A', swapRows]; split_ifs <;> simp
  have h : i < A.size ∧ j < A.size := by
    rw [size_toArray2D_rows M]
    simp [hi, hj]
  have hA' : A'.size = m := by
    simp [A', swapRows]
    simp [h, A]
    exact size_toArray2D_rows M
  have hrect : Rect A' n := by
    intro k hk
    rw [hAA'] at hk
    by_cases hki : k = i
    · simp [hki, A', swapRows, h, Array.setIfInBounds]
      by_cases hij : i = j
      · subst hij
        simpa using hrectA i h.1
      · simp [Array.getElem_set, ne_comm.mp hij, hrectA j]
    · simp [A', swapRows, h, Array.setIfInBounds, Array.getElem_set]
      by_cases hkj : k = j
      · simp [hkj, hrectA i]
      · simp [ne_comm.mp hkj, ne_comm.mp hki, hrectA k]

  (toMat A' m n hA' hrect) = (Matrix.swap α ⟨i, hi⟩ ⟨j, hj⟩) * M := by
  -- 行の成分比較。`swap_mul_apply_left/right` が武器。
  sorry


/- 行スケール: `rowScale i k` は「該当成分だけ k」の対角行列の左乗 -/
def scaleRowMat {m K} [Field K] (i : Fin m) (k : K) :
  Matrix (Fin m) (Fin m) K :=
  diagonal (fun r => if r = i then k else 1)

lemma toMat_rowScale {m n K} [Field K]
  (i j : ℕ) (k : K)
  (M : Matrix (Fin m) (Fin n) K) (hi : i < m) (hj : j < m) :
  let A := toArray2D M
  let A' := rowScale i k A
  let scaleMat := scaleRowMat ⟨i, hi⟩ k
  have hA : i < A.size := by rw [size_toArray2D_rows M]; exact hi
  have hA' : A'.size = m := by simp [A', rowScale, hA]; exact size_toArray2D_rows M
  have hrect : Rect A' n := by
    have hrectA : Rect A n := rect_toArray2D M
    simp [A', rowScale]
    intro k hk
    simp [hA, Array.setIfInBounds, Array.getElem_set]
    by_cases hik : k = i
    · simp [Eq.symm hik, hrectA k]
    · simp [ne_comm.mp hik, hrectA k]

  (toMat A' m n hA' hrect) = Matrix.mulᵣ scaleMat M := by
  -- `Matrix.mul_apply` と `diagonal` の計算
  sorry

/- 行加算: `rowAxpy i k α`（i ← i − α·k）は transvection の左乗 -/
lemma toMat_rowAxpy {m n K} [Field K]
  (i k : ℕ) (α : K)
  (M : Matrix (Fin m) (Fin n) K) (hi : i < m) (hk : k < m) :
  let A := toArray2D M
  have hrectA : Rect A n := rect_toArray2D M
  have hik : i < A.size ∧ k < A.size := by rw [size_toArray2D_rows M]; simp [hi, hk]
  let A' := rowAxpy i k α A n hrectA
  have hA' : A'.size = m := by simp [A', rowAxpy, hik, A]; exact size_toArray2D_rows M
  have hrect : Rect A' n := by
    simp [A', rowAxpy, hik, Array.setIfInBounds]
    intro k hk
    simp [Array.getElem_set]
    by_cases hik_eq : k = i
    · simp [Eq.symm hik_eq]
    · simp [ne_comm.mp hik_eq, hrectA k]

  (toMat A' m n hA' hrect) = Matrix.mulᵣ (Matrix.transvection ⟨i, hi⟩ ⟨k, hk⟩ α) M := by
  admit

/- algorithm result, echelon form rank, original matrix rank -/

/- mod p のある評価で full ランクが出れば、厳密ランク（generic rank）も full。 -/
axiom generic_full_of_modp_full
  (P : Params) (G : Finset (Ground P))
  {p : Nat} [Fact (Nat.Prime p)]
  (α : Var P → ZMod p)
  (hfull : trialRankVar (p := p)
              (A := restrictColsPolyZ P G |> fun M i j =>
                      let toFin := (Fintype.equivFin _).symm
                      M i (toFin j))
              α
           = Nat.min (d_col P) (Fintype.card {e // e ∈ G})) :
  rankQ_exact P G
    = Nat.min (d_col P) (Fintype.card {e // e ∈ G})


/- foldl (max …) の結果が full なら、入力列のどれかで full が達成されている。 -/
lemma exists_trial_hits_full
  (P : Params)
  {p : Nat} [Fact (Nat.Prime p)]
  {αs : List (Var P → ZMod p)}
  (trial : (Var P → ZMod p) → Nat)
  (full : Nat)
  (hbound : ∀ a, trial a ≤ full)
  (hbest : αs.foldl (fun acc a => acc.max (trial a)) 0 = full) :
  ∃ a ∈ αs, trial a = full := by
  -- 素直なリスト帰納法で証明できます（実装は後ででOK）。
  admit

/- 純関数版ハイブリッドは常に厳密ランクと一致する。 -/
theorem rankQ_hybrid_withVar_correct
  (P : Params) (G : Finset (Ground P))
  {p : Nat} [Fact (Nat.Prime p)]
  (alphas : List (Var P → ZMod p)) :
  rankQ_hybrid_withVar P G (p := p) alphas = rankQ_exact P G := by
  classical
  -- 記号をそろえる
  let d    := d_col P
  let m    := Fintype.card {e : Ground P // e ∈ G}
  let full := Nat.min d m
  -- Z 係数の多項式行列（列制限）
  let toFin : Fin m → {e : Ground P // e ∈ G} := (Fintype.equivFin _).symm
  let MpolyZ : Matrix (Fin d) (Fin m) (MvPolynomial (Var P) Int) :=
    fun i j => (restrictColsPolyZ P G) i (toFin j)
  -- trial と best
  let trial : (Var P → ZMod p) → Nat :=
    fun α => trialRankVar (p := p) (A := MpolyZ) α
  have hbound : ∀ α, trial α ≤ full := by
    intro α; exact le_of_lt_or_eq (by exact Nat.le_of_lt_succ (Nat.le_of_lt_succ (Nat.le_max_left _ _))) -- （簡単：rank ≤ min d m）
    -- ↑ ここは「行列ランク ≤ min(d,m)」の一般事実で埋める（あとで差し替え）
  let best := alphas.foldl (fun acc α => Nat.max acc (trial α)) 0
  -- 定義に沿って分岐
  dsimp [rankQ_hybrid_withVar]  -- if h : best = full then … else …
  by_cases hbest : best = full
  · -- 早期終了の分岐：best=full ⇒ どこかで trial α = full
    have ⟨α, hmem, hα⟩ := exists_trial_hits_full (P:=P) (G:=G)
                              trial full hbound hbest
    -- その α で mod p full ⇒ generic full
    have hgen := generic_full_of_modp_full (P:=P) (G:=G) (p:=p) α hα
    -- if 分岐の値は full。よって exact も full。
    simpa [hbest, hgen]
  · -- best < full ：定義どおり exact を返す
    simp []

/- IO ラッパの結果は常に厳密ランクと一致。 -/
theorem rankQ_hybrid_IO_correct
  (P : Params) (G : Finset (Ground P))
  (p : Nat) [Fact (Nat.Prime p)]
  (trials : Nat := 2) :
  (do let r ← Checker.rankQ_hybrid_IO P G p (trials := trials); pure r)
  = pure (Checker.rankQ_exact P G) := by
  -- 定義を展開して、任意に生成された alphas に対して
  -- rankQ_hybrid_withVar_correct を当てるだけ（IO の結合律を使って書き換え）。
  admit


-- 「列独立 ↔ “（ハイブリッド仕様が返す）rank = 列数”」
axiom rankQ_correct
  (P : Params) (G : Finset (Ground P)) :
  (LM.ColsIndependentOn (M := St.M P) G) ↔ (Checker.rankQ_exact P G = G.card)


-- rank ベースの Bool 判定
noncomputable def Checker.allColsIndependentBool
  (P : Params) (G : Finset (Ground P)) : Bool :=
  decide (Checker.rankQ_exact P G = G.card)

-- 正しさ：Bool = true ↔ indep
theorem allColsIndependentBool_correct
  (P : Params) (G : Finset (Ground P)) :
  Checker.allColsIndependentBool P G = true ↔ St.indep P G := by
  classical
  -- decide の等価：`decide (A) = true ↔ A`
  have hdec :
    Checker.allColsIndependentBool P G = true
      ↔ (Checker.rankQ_hybrid_withVar P G = G.card) := by
    -- A :≡ (rank = |G|)
    let A := Checker.rankQ_hybrid_withVar P G = G.card
    -- A で場合分けして simp すれば Bool ↔ Prop
    by_cases h : A
    · simp [Checker.allColsIndependentBool, A, h]
    · simp [Checker.allColsIndependentBool, A, h]
  -- rank 仕様 ↔ indep（公理）
  have hspec := (rankQ_correct P G).symm
  -- 合成して完成
  exact hdec.trans hspec



/- まずは `findCircuit` の仕様（探索順序に依存する“公理化”）。
   実装が固まったらこの axiom は lemma に置き換えて OK。 -/
-- TODO: 将来証明する
axiom Checker.findCircuit_spec
  (P : Params) (G : Finset (Ground P)) :
  ∀ {C : Finset (Ground P)}, Checker.findCircuit P G = some C →
    (C ⊆ G) ∧ (¬ St.indep P C) ∧ (∀ e ∈ C, St.indep P (C.erase e))

/- `findCircuit` の健全性：some C なら本当に Sₜ-サーキット -/
theorem findCircuit_sound
  (P : Params) (G : Finset (Ground P)) :
  ∀ {C : Finset (Ground P)}, Checker.findCircuit P G = some C → St.isCircuit P C := by
  classical
  intro C hC
  -- 仕様から：C ⊆ G, ¬indep C, ∀e∈C, indep (C.erase e)
  rcases Checker.findCircuit_spec P G hC with ⟨_hCsub, hdep, hmin⟩
  -- `St.isCircuit` の定義は `¬indep C ∧ ∀ e∈C, indep (C.erase e)`
  unfold St.isCircuit
  refine And.intro ?notIndep ?minIndep
  · -- 従属性
    simpa [St.indep] using hdep
  · -- 各辺を外せば独立
    intro e he
    simpa [St.indep] using hmin e he


/- `closureFinset` の正しさ（Finset/Set/Prop の一致：型だけ）。
今は `closureFinset` を `St.closure` に委譲しているので、将来計算版に
差し替えるときのための仕様定理として置いておく。 -/
theorem closureFinset_correct
  (P : Params) (C : Finset (Ground P)) :
  -- 例：`e ∈ closureFinset …` ↔ `e ∈ closureSet …` をあとで証明する想定
  True := by
  trivial

end CheckerCorrectness


namespace EquivGoal

open St Cnt

/-! ## サーキット存在（マトロイド一般論；Params 版）
`G` が Sₜ-従属なら、`G` に含まれるサーキットが存在する。 -/
/- If `G` is Sₜ-dependent, then there exists a circuit `C ⊆ G`. -/
axiom circuit_exists_of_St_dep
  (P : Params) (G : Finset (Ground P)) :
  (¬ St.indep P G) → ∃ C : Finset (Ground P), C ⊆ G ∧ St.isCircuit P C

/-! ## 補題4（PDF）Params 版（大域同値）
(a) `∀ G, CtIndependent P G → St.indep P G`
↔ (b) `∀ C, St.isCircuit P C → InCnt P (St.closure P C)` -/
/- Lemma 4 (global, Params form). -/
axiom Lemma4_global (P : Params) :
  (∀ G : Finset (Ground P), Cnt.CtIndependent P G → St.indep P G) ↔
  (∀ C : Finset (Ground P), St.isCircuit P C → Cnt.InCnt P (St.closure P C))

/- 対偶： (b) を否定する回路が 1 つでもあれば、(a) の否定すなわち
   `∃ G, CtIndependent P G ∧ ¬ St.indep P G` が成り立つ。 -/
lemma lemma4_right_contrapositive (P : Params) :
  (∃ C : Finset (Ground P), St.isCircuit P C ∧ ¬ Cnt.InCnt P (St.closure P C)) →
  (∃ G : Finset (Ground P), Cnt.CtIndependent P G ∧ ¬ St.indep P G) := by
  classical
  intro hex
  -- 「(b) が ∀C… 成立しない」ことを作る
  have hnotB :
      ¬ (∀ C : Finset (Ground P), St.isCircuit P C → Cnt.InCnt P (St.closure P C)) := by
    rcases hex with ⟨C, hC, hnot⟩
    intro hforall; exact hnot (hforall C hC)
  -- 同値から (a) も成立しない
  have hnotA :
      ¬ (∀ G : Finset (Ground P), Cnt.CtIndependent P G → St.indep P G) :=
    (mt (Lemma4_global P).mp) hnotB
  -- ∃G … を取り出す
  simpa [not_forall] using hnotA

end EquivGoal



/-! ## アルゴリズム（Bool）の仕様と正しさ（型）

  check G の実装は AppendixB 名前空間側にあり、ここでは結果との同値を固定。
-/

namespace AppendixB

open Checker St Cnt EquivGoal

/- True 側仕様は維持（St-dep かつ 「G 内の回路 C」で cl(C) ∉ 𝒞） -/
def check_spec_true (P : Params) (G : Finset (Ground P)) : Prop :=
  Cnt.StDependent P G ∧
  ∃ C : Finset (Ground P), C ⊆ G ∧ St.isCircuit P C ∧ ¬ Cnt.InCnt P (St.closure P C)

/- False 側仕様は「その G が反例でない」に一本化 -/
def check_spec_false (P : Params) (G : Finset (Ground P)) : Prop :=
  ¬ Cnt.Counterexample P G

/- Appendix B の反例判定器（骨格実装；Params 版）。
   1) S_t-independent なら `false`
   2) そうでなく回路 C を見つけ、cl(C) ∈ 𝒞_{n,t} なら `false`
   3) cl(C) ∉ 𝒞_{n,t} なら `true`
   ※ findCircuit P G = none の場合は保守的に `false`。 -/
/- 実行時に追跡したい中間情報。 -/
structure CheckTrace (P : Params) where
  rank : ℕ                                    -- (2) G のランク
  indep   : Bool                                 -- (2) 独立？（= rank = |G|）
  circuit? : Option (Finset (Ground P))          -- (3) 見つかったサーキット
  closure? : Option (Finset (Ground P))          -- (4) その閉包
  inCnt?  : Option Bool                          -- (5) 閉包 ∈ 𝒞_{n,t}？
  result  : Bool                                 -- 返却値（= check と同じ）

/- 5 ステップをそのまま実行し、途中の値も返すトレース版。 -/
noncomputable def runTrace (P : Params) (G : Finset (Ground P)) : CheckTrace P := by
  classical
  -- (2) rank と独立判定
  let r := Checker.rankQ_exact P G
  let indep : Bool := decide (r = G.card)
  -- (1),(2) で独立なら false を返す（回路も閉包も無し）
  if h : indep = true then
    exact {
      rank    := r
      indep   := indep
      circuit? := none
      closure? := none
      inCnt?  := none
      result  := false
    }
  else
    -- (3) サーキット探索
    match Checker.findCircuit P G with
    | none =>
        -- 従属のはずだが見つからなければ保守的に false
        exact {
          rank    := r
          indep   := indep
          circuit? := none
          closure? := none
          inCnt?  := none
          result  := false
        }
    | some C =>
        -- (4) 閉包計算（ここでは仕様版 `St.closure` に委譲）
        let cl := St.closure P C
        -- (5) 閉包が 𝒞_{n,t} に入るか？
        if hcl : Cnt.InCnt P cl then
          exact {
            rank    := r
            indep   := indep
            circuit? := some C
            closure? := some cl
            inCnt?  := some true
            result  := false
          }
        else
          exact {
            rank    := r
            indep   := indep
            circuit? := some C
            closure? := some cl
            inCnt?  := some false
            result  := true
          }

/- 既存の Bool 版 `check` と同じ判定だけ欲しい人向けの薄いラッパ。 -/
noncomputable def check (P : Params) (G : Finset (Ground P)) : Bool :=
  (runTrace P G).result

/- 実装後に満たすべき仕様（axiom; 骨格） -/
-- TODO: 将来証明する
axiom check_true_iff (P : Params) (G : Finset (Ground P)) :
  check P G = true  ↔ check_spec_true  P G
-- TODO: 将来証明する
axiom check_false_iff (P : Params) (G : Finset (Ground P)) :
  check P G = false ↔ check_spec_false P G

end AppendixB


namespace AppendixBCorrectness
open Cnt St AppendixB EquivGoal

/-! sound（True側）：check P G = true → 反例が「存在する」 -/
theorem sound (P : Params) (G : Finset (Ground P)) :
  check P G = true → ExistsCounterexample P := by
  intro h
  -- 仕様を展開
  have hspec : check_spec_true P G := (check_true_iff P G).1 h
  rcases hspec with ⟨hdep, ⟨C, hCsub, hC, hnot⟩⟩
  -- 「cl(C) ∉ 𝒞_{n,t}」なる回路が Ground(P) 上に存在 ⇒ 補題4の対偶（大域）で反例が存在
  have hx : ∃ C, St.isCircuit P C ∧ ¬ Cnt.InCnt P (St.closure P C) := ⟨C, hC, hnot⟩
  exact lemma4_right_contrapositive P hx

/-! complete（False側）：check P G = false → その G は反例ではない -/
theorem complete (P : Params) (G : Finset (Ground P)) :
  check P G = false → ¬ Counterexample P G := by
  intro h
  -- 仕様そのもの
  have hspec : check_spec_false P G := (check_false_iff P G).1 h
  exact hspec

/- True 側：check が true なら「どこかに」反例が存在する。 -/
theorem check_true_implies_exists_counterexample
  (P : Params) (G : Finset (Ground P)) :
  check P G = true → ExistsCounterexample P :=
  sound P G

/- 逆向き：もし G 自身が反例なら，チェックは必ず true を返す。 -/
theorem counterexample_implies_check_true
  (P : Params) (G : Finset (Ground P)) :
  Counterexample P G → check P G = true := by
  intro hCE
  -- False なら「反例ではない」に反するので，False は起こりえない
  have hnotfalse : ¬ check P G = false := by
    intro hf
    exact (complete P G hf) hCE
  -- Bool の二値性で結論
  by_cases hc : check P G = true
  · exact hc
  · -- 2値なので false しかないが，それは上の hnotfalse と矛盾
    cases hcb : check P G <;> simp [hcb] at *


end AppendixBCorrectness
