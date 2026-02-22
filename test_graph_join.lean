import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

-- ヘルパー: 頂点をシフトして K1 (頂点0) と結合する (実行可能な実装)
def graph_join_K1 {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph (Fin (n + 1)) :=
  SimpleGraph.fromRel (fun u v =>
    match u, v with
    | ⟨0, _⟩, ⟨0, _⟩ => False
    | ⟨0, _⟩, _ => True
    | _, ⟨0, _⟩ => True
    | ⟨u'+1, hu⟩, ⟨v'+1, hv⟩ => G.Adj ⟨u', by omega⟩ ⟨v', by omega⟩
  )

-- 保証1: 頂点 0 と 頂点 0 は結合されない (SimpleGraph のループなし制約の確認)
@[simp]
theorem graph_join_K1_not_adj_zero_zero {n : ℕ} (G : SimpleGraph (Fin n)) :
  ¬ (graph_join_K1 G).Adj 0 0 := by
  intro h
  simp only [graph_join_K1, SimpleGraph.fromRel_adj] at h
  exact h.1 rfl

-- 保証2: 頂点 0 は、0 以外のすべての頂点 (v.succ) と結合される
@[simp]
theorem graph_join_K1_adj_zero_succ {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
  (graph_join_K1 G).Adj 0 v.succ := by
  simp only [graph_join_K1, SimpleGraph.fromRel_adj]
  refine ⟨by simp [Fin.ext_iff], ?_⟩
  left
  show (match (⟨0, Nat.zero_lt_succ n⟩ : Fin (n+1)),
            (⟨v.val + 1, by omega⟩ : Fin (n+1)) with
        | ⟨0, _⟩, ⟨0, _⟩ => False
        | ⟨0, _⟩, _ => True
        | _, ⟨0, _⟩ => True
        | ⟨u'+1, hu⟩, ⟨v'+1, hv⟩ => G.Adj ⟨u', by omega⟩ ⟨v', by omega⟩)
  trivial

-- 保証3: 逆に、すべての頂点 (v.succ) は頂点 0 と結合される (対称性)
@[simp]
theorem graph_join_K1_adj_succ_zero {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) :
  (graph_join_K1 G).Adj v.succ 0 := by
  exact (graph_join_K1 G).symm (graph_join_K1_adj_zero_succ G v)

-- 保証4: 元のグラフ G の隣接関係は、シフトされた頂点間で完全に保存される
@[simp]
theorem graph_join_K1_adj_succ_succ {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
  (graph_join_K1 G).Adj u.succ v.succ ↔ G.Adj u v := by
  simp only [graph_join_K1, SimpleGraph.fromRel_adj]
  have hu_eq : (⟨u.val, by omega⟩ : Fin n) = u := Fin.ext rfl
  have hv_eq : (⟨v.val, by omega⟩ : Fin n) = v := Fin.ext rfl
  constructor
  · intro ⟨_, h⟩
    simp only [Fin.succ] at h
    rcases h with h | h
    · rwa [hu_eq, hv_eq] at h
    · rw [hu_eq, hv_eq] at h
      exact h.symm
  · intro h
    refine ⟨?_, ?_⟩
    · intro heq
      exact G.ne_of_adj h (by
        have := congrArg Fin.val heq
        simp [Fin.succ] at this
        exact Fin.ext this)
    · left
      simp only [Fin.succ]
      rwa [hu_eq, hv_eq]

#check @graph_join_K1_not_adj_zero_zero
#check @graph_join_K1_adj_zero_succ
#check @graph_join_K1_adj_succ_succ
