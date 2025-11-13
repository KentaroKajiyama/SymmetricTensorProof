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
    {m n} {α : Type u} [Field α] (A0 : Array (Array α)) (M0 : Matrix (Fin m) (Fin n) α)
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
  ∀ i : Fin r0, ∀ j : Fin n, (j : Nat) < (p0 i : Nat) → (matOf R0) (Fin.castLE I1_bound.1 i) j = 0)
(I4_tail0 :
  ∀ j : Fin n, (j : Nat) < c0 →
    (∀ i : Fin r0, p0 i ≠ j) →
    ∀ i' : Fin m, (r0 : Nat) ≤ (i' : Nat) → (matOf R0) i' j = 0)
(I5_fac :
  ∃ (E : Matrix (Fin m) (Fin m) α), IsUnit E ∧ matOf R0 = E * M0)

lemma inv_init
  {K : Type u} [Field K] {m n : ℕ}
  (A0 : Array (Array K)) (M0 : Matrix (Fin m) (Fin n) K)
  (R0 : Rectified m n K)
  (h0 : matOf R0 = M0) :
  Inv A0 M0 R0 0 0 (Fin.elim0) := by
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
              (A0 := R.A)
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
  doneP st ↔ st.rowCount = m ∨ st.colPtr = n :=
by
  -- これは st.inv.I1_bound : st.rowCount ≤ m ∧ st.colPtr ≤ n を使って示せる。
  -- ここはあとで埋めればいい（sorry でOKにして先に進んでいい）。
  sorry

-- ==============================
-- pivot探索（汎用版）
-- ==============================

/- 最初に i ≥ st.rowCount かつ (matOf st.R)[i, st.colPtr] ≠ 0 を見つける。なければ none。 -/
def findPivot {m n : Nat} {K : Type u} [Field K] (st : GEStateP m n K) : Option (Fin m) :=
  -- 今は単に none にしておく。後で Array.findIdx 等で書き換える
  none

/- pivotが見つからなかった場合、その列はr以降すべて0 -/
lemma findPivot_none_sound
  {m n K} [Field K]
  {st : GEStateP m n K}
  (hcol : st.colPtr < n)
  (h : findPivot st = none) :
  ∀ i : Fin m, (st.rowCount : Nat) ≤ i →
    (matOf st.R) i ⟨st.colPtr, hcol⟩ = 0 :=
  sorry

/- pivotが見つかった場合、そのi0行が確かに非零 -/
lemma findPivot_some_sound
  {m n K} [Field K]
  {st : GEStateP m n K} {i0 : Fin m}
  (hcol : st.colPtr < n)
  (h : findPivot st = some i0) :
  (st.rowCount : Nat) ≤ i0 ∧
  (matOf st.R) i0 ⟨st.colPtr, hcol⟩ ≠ 0 :=
  sorry

-- ==============================
-- Invの保持補題（1ステップ）
-- ==============================

lemma inv_step_none
  {m n K} [Field K] {st : GEStateP m n K}
  (hnone : findPivot st = none)
  : Inv st.R.A st.M0 st.R st.rowCount (st.colPtr + 1) st.pivot :=
  sorry

lemma inv_step_some
  {m n K} [Field K] {st : GEStateP m n K} {i0 : Fin m}
  (hsome : findPivot st = some i0)
  : let R₁ := rSwap st.R st.rowCount i0.val
    let a  := (matOf R₁) ⟨st.rowCount, by sorry⟩ ⟨st.colPtr, by sorry⟩
    let R₂ := rScale R₁ st.rowCount (a⁻¹)
    let R₃ := R₂ -- 実際は各行にrAxpy適用して0消去
    let new_r   := st.rowCount + 1
    let new_c   := st.colPtr + 1
    let new_piv := extendPivot st.pivot ⟨st.colPtr, by sorry⟩
    Inv R₃.A st.M0 R₃ new_r new_c new_piv :=
  sorry

-- ==============================
-- 1ステップ関数
-- ==============================

@[inline] def μ {m n K} [Field K] (st : GEStateP m n K) : Nat := n - st.colPtr

def μ_exec {m n K} [Field K] (st : GEExecState m n K) : Nat := n - st.colPtr


def geStepP {m n K} [Field K] (st : GEStateP m n K) : GEStateP m n K :=
  match findPivot st with
  | none =>
      let new_c := st.colPtr + 1
      have inv' : Inv st.R.A st.M0 st.R st.rowCount new_c st.pivot :=
        inv_step_none (by simp [findPivot])
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
      let a  := (matOf R₁) ⟨st.rowCount, by sorry⟩ ⟨st.colPtr, by sorry⟩
      let R₂ := rScale R₁ st.rowCount (a⁻¹)
      let R₃ := R₂ -- 後でrAxpyで他行消去する
      let new_r   := st.rowCount + 1
      let new_c   := st.colPtr + 1
      let new_piv := extendPivot st.pivot ⟨st.colPtr, by sorry⟩
      have inv' : Inv R₃.A st.M0 R₃ new_r new_c new_piv :=
        -- TODO: findPivot を埋めたらここも埋める
        inv_step_some (by admit)
      { M0 := st.M0, R := R₃, rowCount := new_r, colPtr := new_c, pivot := new_piv, inv := inv' }

def stepKernel {m n K} [Field K] (st : GEExecState m n K)
  : GEExecState m n K :=
  -- ここで findPivot / rSwap / rScale / rAxpy を使って
  -- 「c を必ず +1、pivot 見つかったら r も +1」までを実装
  -- （あなたの geStepP の計算部分だけを抽出）
  sorry


lemma stepP_erases_to_kernel
  {m n K} [Field K] (stP : GEStateP m n K) :
  erase (geStepP stP) = stepKernel (erase stP) :=
by
  -- geStepP の本体（計算部）は stepKernel と同じ、を示す
  -- findPivot の分岐、rSwap/rScale/rAxpy の順を潰す
  sorry


-- 1. 1ステップで M0 は書き換えない（レコード更新が M0 に触れない）
lemma geStepP_preserves_M0 {m n K} [Field K] (s : GEStateP m n K) :
  (geStepP s).M0 = s.M0 := rfl

lemma colPtr_lt_n_of_not_done
  {m n K} [Field K] {s : GEStateP m n K}
  (h : ¬ doneP s) : s.colPtr < n := by
  -- ← あなたの doneP の定義に合わせて証明する
  -- 例： by
  --   rcases (doneP_cases s) with hdone | hdone
  --   · exact False.elim (h hdone)
  --   · … など
  admit

lemma geStepP_decreases_of_lt {m n K} [Field K]
  (s : GEStateP m n K) (hcn : s.colPtr < n) :
  μ (geStepP s) < μ s := by
  cases h : findPivot s with
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
    · exact geRunWF_P (geStepP st)
termination_by st => μ st
decreasing_by
  have hcn : st.colPtr < n := colPtr_lt_n_of_not_done (s:=st) h
    -- strict decrease を適用
  have : μ (geStepP st) < μ st := geStepP_decreases_of_lt (s:=st) hcn
  simpa [geRunWF_P, h] using this

def geRunExec {m n K} [Field K] (fuel : Nat) (st : GEExecState m n K) : GEExecState m n K :=
  -- fuel 回 stepKernel を回す単純ループ（while相当）
  Nat.iterate stepKernel fuel st

lemma reach_final_with_enough_fuel
  {m n K} [Field K]
  (st0 : GEExecState m n K)
  (fuel fuel' : Nat)
  (hge : fuel ≥ fuel')
  (hstop : doneExecP (geRunExec fuel' st0)) :
  geRunExec fuel st0 = geRunExec fuel' st0 :=
by admit


lemma run_erases_to_exec
  {m n K} [Field K] (st : GEStateP m n K) :
  ∃ fuel ≤ μ_exec (erase st),
    erase (geRunWF_P st) = geRunExec fuel (erase st) :=
by
  -- WF再帰の帰納法＋ stepP_erases_to_kernel を使って、
  -- 各ステップで erase が一致すること（bisim）を示す。
  sorry

theorem geRunExec_correct
  {m n K} [Field K]
  (M0 : Matrix (Fin m) (Fin n) K)
  (fuel : Nat) (hfuel : fuel ≥ n) :
  let R0  : Rectified m n K := rectifiedOfMatrix M0
  let h0  : matOf R0 = M0 := matOf_rectifiedOfMatrix (K:=K) M0
  let _hInv0 : Inv R0.A M0 R0 0 0 (Fin.elim0) := inv_init R0.A M0 R0 h0
  let st0E : GEExecState m n K :=
    { M0 := M0, R := R0, rowCount := 0, colPtr := 0, piv := (Fin.elim0) }
  let outE := geRunExec fuel st0E
  ∃ ref_meta : REFMeta m n,
      IsREF (matOf outE.R) ref_meta ∧
      ref_meta.r = outE.rowCount ∧
      Matrix.rank (matOf outE.R) = outE.rowCount ∧
      Matrix.rank (matOf outE.R) = Matrix.rank M0 :=
by
  intro R0 h0 _hInv0 st0E outE
  -- 以下は前回スケルトンと同様。
  -- 1) run_erases_to_exec で WF⇔Exec の合致
  -- 2) I5_fac と rank_mul_preserved_by_left_unit で rank(M_final)=rank(M0)
  -- 3) IsREF → rank = pivot
  -- 4) pivot 段数 = outE.rowCount を合致させて締める
  sorry



/- Inv の I5 を使えば 元の行列の rank と最後の行列の rank が等しいことが geRun を使った場合でも示せるはず（geRun は Inv を保持するので）。-/
/-- REF の rank はピボット本数に等しい -/
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

  let A_lin : (Fin n → K) →ₗ[K] (Fin m → K) := Matrix.mulVecLin A

  have range_le :
    LinearMap.range A_lin
      ≤ Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i))) := by
    -- range は列ベクトルの像の張る空間。基底 e_j を通した像が col j。
    -- よって各 col j が上の span に入る ⇒ range 全体が入る。
    refine LinearMap.range_le_iff_comap.2 ?_
    intro v
    -- v が基底 e_j なら …
    -- 実務上は `by intro j; simpa using all_cols_in_span j` で OK
    intro j; simpa using all_cols_in_span j

  -- 逆側：pivot 列は range に入る（もちろん列だから）
  have span_le_range :
    Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.pivot i)))
      ≤ (Matrix.toLinearMap A).range := by
    refine Submodule.span_le.2 ?_
    intro v hv
    rcases hv with ⟨i, rfl⟩
    -- `A.col (ref.p i)` は e_(ref.p i) を A に通した像
    refine ⟨Pi.single (ref.p i) 1, ?_⟩
    -- `toLinearMap` で `Pi.single` は「その列」を返す
    -- `Matrix.toLinearMap_apply` or `Matrix.mulVec` 経由の `col` 同一視を使ってください
    -- 多くの環境で `by funext; simp [Matrix.toLinearMap_apply, Matrix.col_apply]` で通ります
    funext i'
    -- ここは
    --   (toLinearMap A) (Pi.single (ref.p i) 1)) i'
    -- = Σ_j A i' j * (Pi.single (ref.p i) 1) j
    -- = A i' (ref.p i)
    -- = (A.col (ref.p i)) i'
    -- の計算です。
    simp [Matrix.toLinearMap_apply, Matrix.col_apply]

  -- 次元（=rank）を挟み撃ち：range と span が相互包含だから同次元
  have eq_spaces :
    (Matrix.toLinearMap A).range
      = Submodule.span K (Set.range (fun i : Fin ref.r => A.col (ref.p i))) :=
    le_antisymm range_le span_le_range

  -- 左辺の finrank が rank、右辺は「LI な ref.r 本の張る空間」だから次元 ref.r
  -- `linInd_pivots` から `finrank_span_eq_card` 系の補題を使う
  have : finrank K ((Matrix.toLinearMap A).range) = ref.r := by
    -- 右辺空間の finrank を計算
    -- `LinearIndependent.finrank_span` の類を使います
    --   finrank(span(range v)) = card(ι) if v は LI
    simpa [eq_spaces] using
      (linInd_pivots.finrank_span (f := fun i : Fin ref.r => A.col (ref.p i)))

  -- rank の定義で仕上げ
  simpa [Matrix.rank] using this

-- TODO: 示す
lemma rank_mul_preserved_by_left_unit
  {m n K} [Field K] {E : Matrix (Fin m) (Fin m) K} {M : Matrix (Fin m) (Fin n) K}
  (hE : IsUnit E) :
  Matrix.rank (E * M) = Matrix.rank M
  := by
  have hdet : IsUnit (Matrix.det E) := (Matrix.isUnit_iff_isUnit_det (A := E)).mp hE
  exact rank_mul_eq_right_of_isUnit_det E M hdet

/- 例：WF 版の最終状態と実行版の最終状態の R が一致する/行空間が一致する等 -/
-- lemma exec_matches_wf {m n K} [Field K]
--   (st : GEStateP m n K) (fuel : Nat) :
--   matOf (geRunWF_P st).R = matOf (geRunExec fuel (erase st)).R := by
--   -- run_erases_to_exec を使って示す
--   sorry

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
    have hdec : μ (geStepP s) < μ s := geStepP_decreases_of_lt s hcn
    have ih'  : doneP (geRunWF_P (geStepP s)) := ih (geStepP s) hdec
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
  ∀ s : GEStateP m n K, (geRunWF_P s).M0 = s.M0 :=
by
  intro s0
  have wf : WellFounded (fun a b : GEStateP m n K => μ a < μ b) := (measure μ).wf
  refine wf.induction (C := fun s => (geRunWF_P s).M0 = s.M0) s0 ?step
  intro s ih
  by_cases hdone : doneP s
  · simp [geRunWF_P, hdone]
  · have hcn : s.colPtr < n := colPtr_lt_n_of_not_done (s:=s) hdone
    have hdec : μ (geStepP s) < μ s := geStepP_decreases_of_lt s hcn
    have ih' := ih (geStepP s) hdec
    rw [geRunWF_P]
    simp [hdone]
    rw [ih']
    exact geStepP_preserves_M0 s

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
    , inv := inv_init R0.A M0 R0 h0 }

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
