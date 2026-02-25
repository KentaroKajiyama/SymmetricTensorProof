import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card

set_option linter.style.longLine false

namespace Claim4GraphEnum.Spec

-- グラフの隣接関係などの決定可能性を自動で解決するために古典論理を使用
attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-
  単純グラフ G に辺 {u, v} を追加する操作の直接的な定義。
  SimpleGraph の構造体として定義することで、Adj, symm, loopless の性質を直接持たせます。
-/
def add_edge [DecidableEq (Fin n)]
    (G : SimpleGraph (Fin n)) (u v : Fin n)
    (huv : u ≠ v) : SimpleGraph (Fin n) where
  Adj := fun i j => G.Adj i j ∨ (i = u ∧ j = v) ∨ (i = v ∧ j = u)
  symm := by
    intro i j h
    rcases h with hG | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left; exact G.symm hG
    · right; right; constructor <;> rfl
    · right; left; constructor <;> rfl
  loopless := by
    intro i h
    rcases h with hG | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact G.loopless i hG
    · exact absurd rfl huv
    · exact absurd rfl huv

lemma neighborFinset_add_edge [DecidableEq (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : u ≠ v) [DecidableRel (add_edge G u v huv).Adj] :
    (add_edge G u v huv).neighborFinset u = insert v (G.neighborFinset u) := by
  ext x
  simp [SimpleGraph.mem_neighborFinset, add_edge, huv]
  tauto

lemma neighborFinset_add_edge_symm [DecidableEq (Fin n)] (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : u ≠ v) [DecidableRel (add_edge G u v huv).Adj] :
    (add_edge G u v huv).neighborFinset v = insert u (G.neighborFinset v) := by
  ext x
  simp [SimpleGraph.mem_neighborFinset, add_edge]
  tauto

/- 方法2: 辺の付加（頂点数 n → n）
  隣接しない次数3の2頂点間に辺を追加する -/
def Method2_Rel (G G' : SimpleGraph (Fin n)) : Prop :=
  ∃ v1 v2 : Fin n,
    ∃ (h_neq : v1 ≠ v2),
    G.degree v1 = 3 ∧ G.degree v2 = 3 ∧
    ¬G.Adj v1 v2 ∧
    G' = add_edge G v1 v2 h_neq

/- 頂点分割の構成情報（方法3-b用）-/
structure SplitConfig (n : ℕ) (G : SimpleGraph (Fin n)) where
  w : Fin n
  hw_deg : G.degree w = 4
  N1 : Finset (Fin n)
  N2 : Finset (Fin n)
  h_partition : N1 ∪ N2 = G.neighborFinset w
  h_disjoint : Disjoint N1 N2
  h_card1 : N1.card = 2
  h_card2 : N2.card = 2

/- 方法3-b: 頂点の分割（頂点数 n → n+1）
  次数4の頂点wを2つの次数3の頂点v1, v2に分割する。
  (実装上は、w を v1 として再利用し、新しい頂点 n を v2 として追加するのが一般的です) -/
def Method3b_Rel (G : SimpleGraph (Fin n)) (G' : SimpleGraph (Fin (n + 1))) : Prop :=
  ∃ (cfg : SplitConfig n G),
    let v1 : Fin (n + 1) := Fin.castSucc cfg.w
    let v2 : Fin (n + 1) := Fin.last n
    -- 1. 旧頂点間の辺（wに接続しないもの）は保持
    (∀ (x y : Fin n), x ≠ cfg.w → y ≠ cfg.w →
      (G'.Adj (Fin.castSucc x) (Fin.castSucc y) ↔ G.Adj x y)) ∧
    -- 2. w (v1) と N1 の間に辺
    (∀ (x : Fin n), x ≠ cfg.w →
      (G'.Adj v1 (Fin.castSucc x) ↔ x ∈ cfg.N1)) ∧
    -- 3. 新頂点 (v2) と N2 の間に辺
    (∀ (x : Fin n), x ≠ cfg.w →
      (G'.Adj v2 (Fin.castSucc x) ↔ x ∈ cfg.N2)) ∧
    -- 4. v1 と v2 の間に辺
    G'.Adj v1 v2

/- 頂点置換の構成情報（方法1用）-/
structure Method1Config (n : ℕ) (G : SimpleGraph (Fin n)) where
  v1 : Fin n
  v2 : Fin n
  h_adj : G.Adj v1 v2
  h_deg1 : G.degree v1 = 3
  h_deg2 : G.degree v2 = 3
  -- X1 = N(v1) \ {v2} の2要素
  x1a : Fin n
  x1b : Fin n
  h_x1 : {x1a, x1b} = G.neighborFinset v1 \ {v2}
  h_x1_neq : x1a ≠ x1b
  -- X2 = N(v2) \ {v1} の2要素
  x2a : Fin n
  x2b : Fin n
  h_x2 : {x2a, x2b} = G.neighborFinset v2 \ {v1}
  h_x2_neq : x2a ≠ x2b

/- 方法1: 頂点置換による次数増加（頂点数 n → n+2）
  隣接する次数3の2頂点をK4に置換する。 -/
def Method1_Rel (G : SimpleGraph (Fin n)) (G' : SimpleGraph (Fin (n + 2))) : Prop :=
  ∃ (cfg : Method1Config n G),
    -- v1, v2 を再利用し、新たに頂点 n, n+1 を追加して K4 を形成する
    let u1 : Fin (n + 2) := Fin.castAdd 2 cfg.v1
    let u2 : Fin (n + 2) := Fin.castAdd 2 cfg.v2
    let u3 : Fin (n + 2) := ⟨n, by omega⟩     -- 新頂点 n
    let u4 : Fin (n + 2) := ⟨n + 1, by omega⟩ -- 新頂点 n+1
    let U : Finset (Fin (n + 2)) := {u1, u2, u3, u4}
    -- 1. 旧頂点間 (v1, v2 に関係しないもの) の辺はそのまま
    (∀ (x y : Fin n), x ≠ cfg.v1 → x ≠ cfg.v2 → y ≠ cfg.v1 → y ≠ cfg.v2 →
      (G'.Adj (Fin.castAdd 2 x) (Fin.castAdd 2 y) ↔ G.Adj x y)) ∧
    -- 2. U 内部は完全グラフ K4 をなす (任意の異なる2頂点間に辺がある)
    (∀ (x y : Fin (n + 2)), x ∈ U → y ∈ U → x ≠ y → G'.Adj x y) ∧
    -- 3. U と外部 (X1, X2) の接続
    (∀ (x : Fin n), x ≠ cfg.v1 → x ≠ cfg.v2 →
      (G'.Adj u1 (Fin.castAdd 2 x) ↔ x = cfg.x1a) ∧
      (G'.Adj u3 (Fin.castAdd 2 x) ↔ x = cfg.x1b) ∧
      (G'.Adj u2 (Fin.castAdd 2 x) ↔ x = cfg.x2a) ∧
      (G'.Adj u4 (Fin.castAdd 2 x) ↔ x = cfg.x2b))

end Claim4GraphEnum.Spec
