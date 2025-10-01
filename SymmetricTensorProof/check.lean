import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Basic
import Mathlib.Data.Sym.Sym2

open scoped BigOperators
open Matrix

/- マトロイドの要素の基本パラメータ -/
structure Instance where
  n : ℕ           -- 頂点数
  t : ℕ           -- テンソル次数
  edges : List (Sym2 (Fin n))  -- 辺の順序（(min,max)で固定）


/- 係数体は ℚ。多変数多項式 ℚ[X] -/
abbrev K := ℚ
/- 変数: 各頂点 i と座標 a に対し x_(i,a) を用意 -/
abbrev Var (inst : Instance) : Type := Fin inst.n × Fin inst.t
abbrev Kpoly (inst : Instance) := MvPolynomial (Var inst) K

/-- 上三角 (r ≤ c) のインデックスの `List`（r 外側, c 内側） -/
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

/-- 上三角の個数は t(t+1)/2 -/
lemma upperPairs_length (t : ℕ) :
  (upperPairs t).length = t * (t+1) / 2 := by
  -- ★ ここは Appendix の組合せ等式に対応：∑_{r=0}^{t-1} (t-r)
  -- List.finRange / bind / if 分岐の長さを数えるだけ
  -- mathlib にある類似補題で短く書けますが、最初は `by
  --   induction' t with t ih ...` で帰納してもOK
  admit

/-- 変数ベクトル p_i = (X_{(i,0)},...,X_{(i,t-1)}) -/
noncomputable def pVec (inst : Instance) (i : Fin inst.n) : Vector (Kpoly inst) inst.t :=
  Vector.ofFn (fun a : Fin inst.t => MvPolynomial.X (i, a))

/-- S_uv = pu*pvᵀ + pv*puᵀ の (r,c) 成分 -/
noncomputable def symOuterEntry (inst : Instance) (u v : Fin inst.n)
  (r c : Fin inst.t) : Kpoly inst :=
  (pVec inst u).get r * (pVec inst v).get c
+ (pVec inst v).get r * (pVec inst u).get c

/-- φ をまず List で（上三角を行優先で並べる） -/
noncomputable def phiList (inst : Instance) (e : Sym2 (Fin inst.n)) :
  List (Kpoly inst) := by
  classical
  -- e の代表元 p : (Fin n × Fin n) を非構成的に取り出す
  let p : (Fin inst.n × Fin inst.n) :=
    Classical.choose (Quot.exists_rep e)
  -- 対応する等式（その p が e の代表である）
  have hp : Quot.mk (Sym2.Rel (Fin inst.n)) p = e :=
    Classical.choose_spec (Quot.exists_rep e)
  -- p を (u,v) に分解
  let u : Fin inst.n := p.1
  let v : Fin inst.n := p.2
  -- 代表元 (u,v) を使って上三角を列挙
  exact (upperPairs inst.t).map (fun ⟨⟨r,c⟩, _rc⟩ =>
    symOuterEntry inst u v r c)

/-- φ: edge → K^{d}（d = t(t+1)/2）。List から Vector に昇格 -/
noncomputable def phi (inst : Instance) (e : Sym2 (Fin inst.n)) :
    Vector (Kpoly inst) (inst.t * (inst.t+1) / 2) := by
  classical
  let xs := phiList inst e
  -- まず phiList 自体の長さを等式にする
  have hx₀ : (phiList inst e).length = inst.t * (inst.t+1) / 2 := by
    -- map は長さを変えない
    -- phiList = (upperPairs t).map ...
    -- よって length phiList = length (upperPairs t)
    simpa [phiList, List.length_map] using upperPairs_length inst.t

  -- それを xs に移し替える（xs は phiList inst e の別名だから）
  have hx : xs.length = inst.t * (inst.t+1) / 2 := by
    simpa [xs] using hx₀

  -- List → Vector（長さ = xs.length）→ 長さを hx でキャストして目標の長さへ
  exact (Vector.cast hx (Vector.ofFn (fun i => xs.get i)))

/- 行列 V_G (d × m)。列は edges の φ。TODO: 列数を t(t+1)/2 に調整する。 -/
noncomputable def VG
  (inst : Instance) :
  Matrix (Fin (inst.t * (inst.t+1)/2)) (Fin inst.edges.length) (Kpoly inst) :=
  fun r c => (phi inst (inst.edges.get c)).get r

/-- ℤ-ベクトルを ℚ[X] の定数ベクトルとして埋める -/
noncomputable def embedZVec (inst : Instance) {m : ℕ} (α : Vector ℤ m) :
  Vector (Kpoly inst) m :=
  Vector.ofFn (fun j : Fin m =>
    MvPolynomial.C ((algebraMap ℤ ℚ) (α.get j)))

/-- 行列×ベクトル（多項式）の積 -/
noncomputable def mulMatVec (inst : Instance) {d m : ℕ}
  (M : Matrix (Fin d) (Fin m) (Kpoly inst))
  (α : Vector (Kpoly inst) m) : Vector (Kpoly inst) d :=
  Vector.ofFn (fun i : Fin d => ∑ j, M i j * α.get j)

/-- 「VG * α = 0（成分ごとに 0 多項式）」を述語にする -/
def MatVecIsZero (inst : Instance) (d : ℕ) (v : Vector (Kpoly inst) d) : Prop :=
  ∀ i, v.get i = 0

/-- 従属証拠：整数ベクトル α ≠ 0 で VG * α = 0（恒等式） -/
structure DepCert (inst : Instance) where
  alphaZ : Vector ℤ inst.edges.length
  nonzero : ∃ j, (alphaZ.get j) ≠ 0
  -- 原始性などは後で足す（仕様次第）

/-- チェック：VG*α が 0 多項式（恒等式） -/
noncomputable def checkDependent (inst : Instance) (c : DepCert inst) : Prop :=
  let α : Vector (Kpoly inst) inst.edges.length := embedZVec inst c.alphaZ
  let M := VG inst
  let v := mulMatVec inst M α
  MatVecIsZero inst (inst.t * (inst.t+1)/2) v

/-- （評価）各 X_(i,a) に有理数を代入する -/
noncomputable def evalAt (inst : Instance)
  (p : Fin inst.n → Fin inst.t → ℚ) :
  MvPolynomial (Var inst) ℚ →+* ℚ :=
  MvPolynomial.eval₂Hom (RingHom.id ℚ) (fun ia => p ia.1 ia.2)

/-- 列インデックスの Finset から `Fin k ↪ Fin m` を作る補助（順序つき） -/
noncomputable def colsEmbedding
  {m : ℕ} (S : Finset (Fin m)) :
  {k : ℕ // k = S.card} × (Fin (S.card) ↪ Fin m) := by
  classical
  -- 典型解：`S.sort` → `List.toEmbedding` → 長さ一致を使って `Fin k ↪ Fin m`
  -- ここは実装テクで、あとで補題化して隠すのがおすすめ
  admit

/-- 独立証拠：列集合 S と、有理数代入 p で det ≠ 0 -/
structure IndCert (inst : Instance) where
  S : Finset (Fin inst.edges.length)   -- |S| = r
  p : (Fin inst.n → Fin inst.t → ℚ)    -- 各変数への代入（整数代入は ℚ に埋め込みでOK）
  detVal : ℚ
  det_ne : detVal ≠ 0
  cardS : S.card = inst.t * (inst.t+1) / 2  -- S の大きさは行数と一致

/-- `VG` の S 列だけを抜いた d×|S| 行列 -/
noncomputable def VGcols (inst : Instance) (S : Finset (Fin inst.edges.length)) :
  Matrix (Fin (inst.t * (inst.t+1)/2)) (Fin S.card) (Kpoly inst) := by
  classical
  let emb := (colsEmbedding S).2
  exact fun r k => (VG inst) r (emb k)

/-- `VGcols` の行列を正方行列にキャスト -/
noncomputable def VGcolsSquare (inst : Instance)
  (S : Finset (Fin inst.edges.length))
  (hS : S.card = inst.t * (inst.t + 1) / 2) :
  Matrix (Fin (inst.t * (inst.t+1) / 2))
         (Fin (inst.t * (inst.t+1) / 2))
         (Kpoly inst) := by
  classical
  -- 元の d×|S| 部分行列
  let Ms := VGcols inst S
  -- 列インデックス `Fin d` を、等式 hS を使って `Fin S.card` にキャストして読む
  -- （Ms は列側が `Fin S.card` なので、`Fin.cast (hS.symm)` でちょうどよい）
  exact fun r c => Ms r (Fin.cast (hS.symm) c)

/-- 評価 φ で det が detVal に一致し非零であることを確認 -/
noncomputable def checkIndependent (inst : Instance) (c : IndCert inst) : Prop :=
  let d  := inst.t * (inst.t + 1) / 2
  let Ms : Matrix (Fin d) (Fin d) (Kpoly inst) :=
    VGcolsSquare inst c.S c.cardS
  let φ  := evalAt inst c.p
  Matrix.det (Matrix.map Ms φ) = c.detVal ∧ c.detVal ≠ 0

/-- 【健全性(従属)】M(X)α=0 が恒等式 ⇒ 任意の代入で列従属 ⇒ generic に従属 -/
theorem sound_dependent (inst : Instance) (c : DepCert inst)
  (h : checkDependent inst c) :
  -- 仕様例：どの代入 p に対しても評価後の列は従属（rank < 列数）
  (∀ p, let φ := evalAt inst p;
        Matrix.rank ((VG inst).map φ) < inst.edges.length) := by
  classical
  -- ここはまだ証明の芯（多項式評価の自然性）を埋める必要があります
  admit

/-- 【健全性(独立)】ある有理点で det ≠ 0 ⇒ det は零多項式でない ⇒ generic に独立 -/
theorem sound_independent
  (inst : Instance) (c : IndCert inst)
  (h : checkIndependent inst c) :
  ∃ p, let φ := evalAt inst p;
      Matrix.det ((VGcolsSquare inst c.S c.cardS).map φ) ≠ (0 : ℚ) := by
  classical
  rcases h with ⟨hval, hne⟩
  refine ⟨c.p, ?_⟩
  -- hval : det ((VGcolsSquare …).map (evalAt inst c.p)) = c.detVal
  -- hne  : c.detVal ≠ 0
  have : Matrix.det ((VGcolsSquare inst c.S c.cardS).map (evalAt inst c.p)) = c.detVal := hval
  -- 右辺の 0 は (0 : ℚ) と明示しておく
  simpa [this] using hne
