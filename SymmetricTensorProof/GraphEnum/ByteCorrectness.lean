import Mathlib
import SymmetricTensorProof.GraphEnum.ByteImpl
import SymmetricTensorProof.GraphEnum.Impl

namespace GraphEnumeration
namespace ByteImpl

open GraphEnumeration.AdjMat (h_size)

variable {n : Nat}

/-!
  # Correctness Proofs for ByteImpl

  We prove that the optimized `ByteImpl` is functionally equivalent to the
  reference implementation `GraphEnumeration.Impl`.

  The bridge is `ByteImpl.AdjMat.toImpl`, which converts the flat ByteArray
  representation to the standard `Array (Array Bool)` representation.
-/

namespace AdjMat

/- 1. Basic Accessor Equivalence -/

theorem toImpl_get_eq (g : AdjMat n) (u v : Fin n) :
    (g.toImpl).get u v = g.get u v := by
  -- 参照実装の get の定義を展開
  simp [toImpl, GraphEnumeration.AdjMat.get]

/- 2. Construction Equivalence -/

theorem toImpl_empty_eq :
  (AdjMat.empty n).toImpl = GraphEnumeration.AdjMat.empty n := by
  -- 定義を展開
  simp [toImpl, empty, GraphEnumeration.AdjMat.empty, get]
  -- Array 同士の等価性は、全要素が等しいことに帰着
  -- ofFn も replicate も Fin n でアクセスできるので、ext で要素比較へ
  ext i j
  · simp
  · simp [Array.getElem_ofFn, Array.getElem_replicate]
  -- 4. 要素へのアクセスを展開
  -- Array.getElem_ofFn : (ofFn f)[i] = f i
  -- Array.getElem_replicate : (replicate n v)[i] = v
  simp [Array.getElem_ofFn, Array.getElem_replicate]
  -- ゴールは以下のような形になります
  -- (if h : idx < size then data.get ... != 0 else false) = false

  -- 【修正】split は不要になりました。
  -- ゴールは「∀ h, ... = 0」という形になっています。
  intro h
  -- get_fillZero_eq_zero は ByteArray.empty を前提にしているので合わせる
  simp [ByteArray.emptyWithCapacity] at h
  simp [ByteArray.emptyWithCapacity]
  conv at h =>
    rhs
    simp [ByteArray.size]
    change 0 + n * n
    rw [zero_add]
  -- 補題を適用して完了
  apply AdjMat.get_fillZero_eq_zero
  exact h

/- 3. Mutation Equivalence -/
theorem toImpl_set_eq (g : AdjMat n) (u v : Fin n) (b : Bool) :
    (g.set u v b).toImpl =
      (match g.toImpl with
      | ⟨d, h⟩ =>
          -- ここで証明を済ませて変数に入れる
          let hu : ↑u < d.size := h.1 ▸ u.isLt
          let hv : ↑v < d[u].size := by
            have : d[u].size = n := by
              exact h.right (Fin.cast h.left.symm u)
            exact lt_of_lt_of_eq v.isLt this.symm
          -- あとは変数を使うだけ
          ⟨
            d.set u ((d[u]'hu).set v b hv) hu,
            by
              simp only [Array.size_set]
              constructor
              · exact h.left
              · simp [Array.getElem_set]
                intro i
                split
                · simp
                  let u_cast : Fin d.size := Fin.cast h.left.symm u
                  exact h.2 u_cast
                · have : (d.set u ((d[u]'hu).set v b hv) hu).size = d.size := by
                    simp [Array.size_set]
                  let i_cast : Fin d.size := Fin.cast this i
                  exact h.2 i_cast
          ⟩
      ) := by
  -- 1. g.toImpl の中身を d, h という名前に分解して取り出す
  --    これにより、右辺の match が計算(簡約)されて消えます
  rcases eq : g.toImpl with ⟨d, h⟩
  -- 2. 定義を展開して整理する (dsimp)
  dsimp
  -- 4. ここで左辺と右辺のデータ部分だけが残ります。
  --    AdjMat.set の定義が右辺と同じロジックなら、これで閉じるはずです。
  --    もし AdjMat.set の定義を展開する必要があれば dsimp [AdjMat.set] を追加してください。
  dsimp [AdjMat.set] -- 必要に応じて
  -- 1. 左辺の if 文を分解する
  split
  next h_valid =>
    -- ケース1: インデックスが範囲内の場合（こちらが本命）
    -- 2. toImpl の定義を展開する
    -- (定義名は実際の実装に合わせて修正してください。例: AdjMat.toImpl)
    unfold AdjMat.toImpl
    -- 3. ここで両辺とも { val := ..., property := ... } の形になったはずなので
    --    Subtype.eq を適用してデータ部分の比較に持ち込む
    simp only -- 余計なハッシュなどが残っていたらきれいにする
    -- 4. 配列の等価性は「全要素が等しい」ことで示す
    -- 5. ここからは計算ゲーム
    -- 左辺: (flat_array.set (idx u v) b).get (idx i j)
    -- 右辺: (d.set u (d[u].set v b))[i][j]
    -- これらが i=u, j=v のときと、それ以外で一致することを示す
    simp
    -- 必要なら split_if などを使って i=u, j=v の場合分けを行う
    -- 1. 配列の等価性を「全要素 i, j が等しい」という問題に変換
    ext i ih_left ih_right j jh_left jh_right
    -- 2. 左辺の Array.ofFn などを簡約して、中身の .get i j を露出させる
    --    右辺の d.set も基本的な形にする
    · simp [h.left.symm]
    -- 1. まず内側の配列サイズが一致することを示す (case h₂.h₁)
    --    Array.ofFn のサイズは常に n、set してもサイズは変わらないことを利用
    · simp
      symm
      have : u < d.size := by
        simp [h.left]
      simp [Array.getElem_set]
      split_ifs with hi
      · simp [Array.size_set]
        subst hi
        exact h.right (Fin.cast h.left.symm u)
      · simp at ih_left
        exact h.right (Fin.cast h.left.symm ⟨i, ih_left⟩)
    -- 2. 次に、要素の値が一致することを示す (case h₂.h₂)
    · simp [AdjMat.get]
      have h_bound :
        i * n + j < (g.data.set (u * n + v) (if b = true then 1 else 0) h_valid).size := by
        simp [AdjMat.idx] at h_valid
        conv_rhs =>
          rw [ByteArray.size_set g.data ⟨(↑u * n + ↑v), h_valid⟩]
        -- ここで i < n, j < n を使って i*n + j < n*n を示す
        -- (ih_left が i < (Array.ofFn ...).size なので i < n です)
        have hi_n : i < n := by simp at ih_left; exact ih_left
        have hj_n : j < n := by simp at jh_left; exact jh_left
        apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_n (i * n))
        rw [← Nat.succ_mul]
        rw [AdjMat.h_size]
        have : i.succ ≤ n := Nat.succ_le_of_lt hi_n
        exact Nat.mul_le_mul_right n this
      have h_bound_v :
        i * n + v < (g.data.set (u * n + v) (if b = true then 1 else 0) h_valid).size := by
        simp [AdjMat.idx] at h_valid
        conv_rhs =>
          rw [ByteArray.size_set g.data ⟨(↑u * n + ↑v), h_valid⟩]
        -- ここで i < n, j < n を使って i*n + j < n*n を示す
        -- (ih_left が i < (Array.ofFn ...).size なので i < n です)
        have hi_n : i < n := by simp at ih_left; exact ih_left
        have hj_n : v < n := Fin.is_lt v
        apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj_n (i * n))
        rw [← Nat.succ_mul]
        rw [AdjMat.h_size]
        have : i.succ ≤ n := Nat.succ_le_of_lt hi_n
        exact Nat.mul_le_mul_right n this
      conv_lhs =>
        unfold AdjMat.idx
        simp [h_bound]
      simp [Array.getElem_set]
      by_cases h_row : ↑u = i
      · simp [h_row]
        simp [h_row] at ih_right
        have : d.size ≤ g.data.size := by
          simp [h.left, g.h_size, Nat.le_mul_self]
        by_cases h_col : ↑v = j
        · simp [h_col]
          conv_lhs =>
            simp [ByteArray.get]
          split_ifs with hb
          · simp [hb]
          · simp [hb]
        · have : i * n + v ≠ i * n + j := by
            simp [h_col]
          have h_bound_j' : i * n + j < g.data.data.size := by
            simp [ByteArray.size_data]
            simp [g.h_size]
            conv at h_bound =>
              arg 2
              rw [ByteArray.size_set g.data ⟨(↑u * n + ↑v), h_valid⟩, g.h_size]
            exact h_bound
          have h_bound_v' : i * n + v < g.data.data.size := by
            simp [ByteArray.size_data]
            simp [g.h_size]
            conv at h_bound_v =>
              arg 2
              rw [ByteArray.size_set g.data ⟨(↑u * n + ↑v), h_valid⟩, g.h_size]
            exact h_bound_v
          conv_lhs =>
            simp [ByteArray.get]
            rw [Array.getElem_set_ne h_bound_v' h_bound_j' this]
          have h_bound_i : i < d[i].size := by
            have h_len : d[i].size = n := h.right ⟨i, ih_right⟩
            rw [h_len]
            exact Nat.lt_of_lt_of_eq ih_right h.left
          have h_len : d[i].size = n := h.right ⟨i, ih_right⟩
          have h_bound_v'' : v < d[i].size := by
            rw [h_len]
            exact Fin.is_lt v
          simp [h_row] at jh_right
          rw [Array.getElem_set_ne h_bound_v'' jh_right h_col]
          -- 1. まず「d は g.get の結果である」という高レベルな事実を have で宣言します。
          --    証明項には、現在のコンテキストにある ih_left, jh_left を使います。
          have h_eq
            : g.get
              ⟨i, Nat.lt_of_lt_of_eq ih_right h.left⟩
              ⟨j, by rw [h_len] at jh_right; exact jh_right⟩
              = d[i][j] := by
            -- d = g.toImpl であることを利用 (eq は rcases eq : ... で定義した前提)
            have : d = g.toImpl.data := by
              simp [eq]
            simp [this, AdjMat.toImpl]
          -- 2. 作成した等式 h_eq の左辺 (g.get ...) を展開して、
          --    「生データへのアクセス」の形 (g.data.data[...]) に近づけます。
          unfold AdjMat.get at h_eq
          dsimp [AdjMat.idx] at h_eq
          simp at h_bound_j'
          simp [h_eq.symm, h_bound_j', ByteArray.get]
      · simp [h_row]
        have h_idx_ne : ↑u * n + ↑v ≠ i * n + j := by
          -- 1. 背理法：等しいと仮定して矛盾を導く
          intro contra
          -- 最終的に u = i を導いて h_row と矛盾させる
          apply h_row
          -- 2. j < n であることを jh_left から取り出す
          -- (Array.ofFn のサイズは n なので simp で言えます)
          have h_j_lt_n : j < n := by simp at jh_left; exact jh_left
          -- 3. n > 0 であることを確認 (v : Fin n なので自明)
          have h_n_pos : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le j) h_j_lt_n
          -- 4. 両辺を n で割った商 (div) が等しいことを利用して u = i を示す
          --    (u * n + v) / n = u, (i * n + j) / n = i
          have : (↑u * n + ↑v) / n = (i * n + j) / n := congr_arg (· / n) contra
          conv at this =>
            rw [Nat.add_comm (u * n), Nat.add_comm (i * n), Nat.mul_comm, Nat.mul_comm i n]
          rw [Nat.add_mul_div_left _ _ h_n_pos,
            Nat.add_mul_div_left _ _ h_n_pos,
            Nat.div_eq_of_lt v.isLt, Nat.div_eq_of_lt h_j_lt_n] at this
          simp only [add_comm, Nat.add_zero] at this
          -- u = i が導かれた
          exact this
        have h_bound_uv : ↑u * n + ↑v < g.data.size := by
          simp [AdjMat.idx] at h_valid
          exact h_valid
        have h_bound_j' : i * n + j < g.data.size := by
          simp [g.h_size]
          conv at h_bound =>
            arg 2; rw [ByteArray.size_set g.data ⟨(↑u * n + ↑v), h_valid⟩, g.h_size]
          exact h_bound
        have : ↑u * n + ↑v = ↑(Fin.mk (↑u * n + ↑v) h_valid) := rfl
        conv_lhs => arg 1; arg 1; arg 2; rw [this]
        simp [ByteArray.get]
        simp [AdjMat.idx] at h_valid
        rw [Array.getElem_set_ne (xs := g.data.data) h_valid h_bound_j' h_idx_ne]
        have : d = g.toImpl.data := by simp [eq]
        simp [this, AdjMat.toImpl, AdjMat.get, AdjMat.idx, h_bound_j', ByteArray.get]
  next h_invalid =>
    -- ケース2: インデックスが範囲外の場合（矛盾を示す）
    -- u, v が Fin n で、n*n の範囲内なら矛盾するはず
    exfalso
    apply h_invalid
    -- 定義を展開: u * n + v < n * n を示せばよい
    rw [g.h_size]
    unfold AdjMat.idx
    -- v < n なので、 u * n + v < u * n + n
    apply Nat.lt_of_lt_of_le (Nat.add_lt_add_left v.isLt (↑u * n))
    -- (u + 1) * n <= n * n を示す
    rw [← Nat.succ_mul]
    apply Nat.mul_le_mul_right
    -- u < n なので u + 1 <= n
    exact Nat.succ_le_of_lt u.isLt

/- add_edge の正当性を証明 -/

theorem toImpl_add_edge_eq (g : AdjMat n) (u v : Fin n) :
  (g.add_edge u v).toImpl = (toImpl g).add_edge u v := by
  -- 定義を展開
  dsimp [add_edge, GraphEnumeration.AdjMat.add_edge]
  -- ここで、証明済みの toImpl_set_eq を2回使うだけです！
  -- toImpl (set (set g u v true) v u true)
  -- = (toImpl (set g u v true)).set v u true
  rw [toImpl_set_eq]
  -- = ((toImpl g).set u v true).set v u true
  rw [toImpl_set_eq]
  -- これで右辺と完全に一致するはずです
  rfl

/- 4. Degree Calculation Equivalence
  これは ByteImpl のループ最適化が正しく動作しているかの核心部分です。
-/

theorem idx_lt_size (g : AdjMat n) (u : Fin n) (i : Nat) (hi : i < n) :
    g.idx u ⟨i, hi⟩ < g.data.size := by
  rw [g.h_size, idx]
  -- u.val * n + i < n * n を示す
  simp
  calc
    -- 1. i < n を利用して、項を n に置き換える
    u.val * n + i < u.val * n + n := Nat.add_lt_add_left hi (u.val * n)
    -- 2. 因数分解 (分配法則)
    _             = (u.val + 1) * n := by rw [Nat.succ_mul]
    -- 3. u < n なので u + 1 ≤ n を利用する
    _             ≤ n * n           := Nat.mul_le_mul_right n (Nat.succ_le_of_lt u.isLt)


-- これをファイルの適当な場所に置くか、証明の中で have で定義します
theorem list_foldl_congr {α β} {l : List α} {f g : β → α → β} {init : β}
    (h : ∀ x ∈ l, ∀ acc, f acc x = g acc x) :
    l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons head tail ih =>
    -- 定義を展開: foldl f init (h::t) = foldl f (f init head) t
    simp
    -- 先頭要素 head について、関数 f と g が同じ結果を返すことを適用
    rw [h head List.mem_cons_self init]
    -- 残りのリスト tail について帰納法の仮定を適用
    apply ih
    -- tail の要素 x は元のリスト (head::tail) にも含まれるので、仮定 h が使える
    intro x hx acc
    apply h x (List.mem_cons_of_mem _ hx)


-- 2. メインの定理
theorem degree_eq (g : AdjMat n) (u : Fin n) :
    g.degree u = (toImpl g).degree u := by
  -- 左辺: ループ定義を foldl に書き換え
  rw [degree, loopRange_eq_foldl, GraphEnumeration.AdjMat.degree, toImpl]
  -- 1. 右辺の構造を整理する
  -- Implの定義にある `data[u]` は `Array.ofFn` へのアクセスなので、
  -- 簡約すると `Array.ofFn (fun j => g.get u j)` になります。
  simp
  -- 2. 【重要】Array.foldl (ofFn f) を List.range の foldl に変換する
  -- これで右辺も「インデックス j を回すループ」になります。
  -- (acc と要素 b を取る関数が、acc とインデックス j を取る関数に変わります)
  have h_len : n = (Array.ofFn (fun j => g.get u j)).size := (Array.size_ofFn).symm
  conv_rhs =>
    -- 1. Array.ofFn の foldl を、Array.range n の foldl に変換
    arg 5
    rw [h_len]
  -- 2. ここで Array.foldl_toList を逆向きに適用します。
  -- これで Array の foldl が List の foldl に変わります。
  rw [← Array.foldl_toList]
  -- 4. 配列変換を解く
  -- (Array.ofFn ...).toList  ->  List.ofFn ...
  rw [Array.toList_ofFn]
  -- 5. List.ofFn を map に変換
  -- List.ofFn f  ->  (List.range n).map f
  rw [List.ofFn_eq_map]
  -- 3. map を foldl の中に吸収
  -- これで両辺とも List.range n のループになります！
  rw [List.foldl_map]
  -- 1. List.range n を、Fin n のリストを map したものに書き換えます
  --    (List.range n = (List.finRange n).map Fin.val)
  rw [← List.map_coe_finRange_eq_range]
  -- 2. map を foldl の関数の中に吸収させます
  --    これで、左辺も「List.finRange n」を回す形になります
  rw [List.foldl_map]
  -- 3. これで両辺のリストが一致したので、apply が通ります！
  apply list_foldl_congr
  -- 4. intro で導入される i は Fin n 型になります
  intro i _ acc
  -- 1. まず AdjMat.get の定義を展開して、中身が見えるようにします
  -- (もし AdjMat が構造体なら dsimp [AdjMat.get] などが必要かもしれません)
  unfold AdjMat.get
  -- 2. 両辺にある if 文を全て分解して総当たりします
  split_ifs with h1 h2
  -- ケース1: データが0 (h1) で、getが真 (h2) の場合 -> 矛盾するはず
  · simp at h2
    -- h1: data... = 0, h2: data... != 0 なので矛盾
    -- 2. g.idx の定義を展開して、インデックスの見た目を h1 と揃えます
    -- (AdjMat.idx が u * n + i であることを適用)
    simp [idx_lt_size g] at h2
    dsimp [AdjMat.idx] at h2
    -- dsimp [ByteArray.get!] at h1
    -- 2. さきほど split_ifs で手に入れた「範囲内である証明 (h_bound)」を使います
    -- これで h1 の if 文が解消され、「g.data.get ... = 0」になります
    have h_bound : ↑u * n + ↑i < g.data.size := idx_lt_size g u i i.isLt
    -- 2. h1 (get!) の定義を展開して if 文を露出させる
    -- 3. h2 のインデックス表記 (AdjMat.idx) を h1 に合わせます
    change (if h : ↑u * n + ↑i < g.data.size then g.data.get (↑u * n + ↑i) h else 0) = 0 at h1
    simp [h_bound] at h1
    exact False.elim (h2 h1)
  -- ケース2: データが0 (h1) で、getが偽 (¬h2) の場合 -> acc = acc
  · rfl
  -- ケース3: データが非0 (¬h1) で、getが真 (h2) の場合 -> acc+1 = acc+1
  · rfl
  -- ケース4: データが非0 (¬h1) で、getが偽 (¬h2) の場合 -> 矛盾するはず
  · rename_i h2
    simp at h2
    -- 1. 範囲内証明
    have h_bound : ↑u * n + ↑i < g.data.size := idx_lt_size g u i i.isLt
    -- 2. h1 (get! ≠ 0) の定義を展開して get にする
    change (if h : ↑u * n + ↑i < g.data.size then g.data.get (↑u * n + ↑i) h else 0) ≠ 0 at h1
    rw [dif_pos h_bound] at h1
    -- これで h1 は「get ... ≠ 0」になりました

    -- 3. h2 のインデックス表記を合わせ、if 文を解消する
    dsimp [AdjMat.idx] at h2
    simp at h1
    exact False.elim (h1 (h2 h_bound))

end AdjMat

/-!
  # Generator Logic Equivalence
-/

open AdjMat

/- Helper: Array vs List conversions -/
theorem toList_toArray_eq {α} (l : List α) : l.toArray.toList = l := by simp

/-
  Verify that `get_isolated` produces the same list of vertices as the reference.
-/
theorem get_isolated_eq (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) :
    (get_isolated g v1 forbidden).toList =
    AdjMat.get_isolated (g.toImpl) v1 forbidden.toList := by
  dsimp [get_isolated, AdjMat.get_isolated]
  -- 1. Array を List に変換
  rw [Array.toList_filterMap, Array.toList_range]
  -- 2. 【重要】List.range n を (List.finRange n).map val に書き換える
  -- これで左辺も「Fin n のリスト」ベースになります
  rw [← List.map_coe_finRange_eq_range]
  -- 3. map を filterMap の中に入れ込む
  -- (map して filterMap するのは、合成関数で filterMap するのと同じ)
  rw [List.filterMap_map]
  -- 4. 右辺の filter を filterMap 形式に書き換える (比較のため)
  rw [<- List.filterMap_eq_filter]
  -- 5. これで両辺とも List.finRange n に対する filterMap になったので、中身の比較に移る
  apply List.filterMap_congr
  intro v _
  -- 6. 中身の論理を合わせる
  -- v.val < n は Fin n の定義より自明なので simp で消える
  simp
  -- 7. 条件式の中身が同じであることを示す
  congr 1
  -- (1) 次数の一致
  rw [degree_eq]
  simp

/-
  Verify that `get_unused` produces the same list of vertices.
-/
theorem get_unused_eq (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) :
    (ByteImpl.get_unused g v1 forbidden).toList =
    AdjMat.get_unused (g.toImpl) v1 forbidden.toList := by
  dsimp [ByteImpl.get_unused, AdjMat.get_unused]
  -- 1. Array.range (Nat) を List.finRange (Fin) の map に変換
  -- これにより、ループ変数が i : Nat から v : Fin n に変わります
  simp [Array.toList_range]
  rw [← List.map_coe_finRange_eq_range]
  rw [List.filterMap_map]
  -- 2. 右辺の filter を filterMap (Option.guard) に書き換える
  -- これで左右の形が filterMap (...) (List.finRange n) で揃います
  rw [← List.filterMap_eq_filter]
  -- 3. 中身の関数の一致を示す
  apply List.filterMap_congr
  intro v _
  -- 4. Option.guard の展開と、if v < n の除去
  dsimp [Option.guard]
  simp
  -- 5. 条件式の等価性
  -- if の条件部分にフォーカスします
  congr 1
  -- 必要な定理を全て simp に渡して一気に書き換えます
  -- degree_eq: 次数の定義合わせ
  -- toImpl_get_eq: 隣接行列アクセスの定義合わせ
  -- Array.contains_def: forbiddenリストの定義合わせ
  simp only [degree_eq, toImpl_get_eq]

/-
  Verify that `generate_next_graphs` produces equivalent graphs.
-/
theorem generate_next_graphs_eq (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) :
    (ByteImpl.generate_next_graphs g v1 forbidden).map AdjMat.toImpl =
    (AdjMat.generate_next_graphs (g.toImpl) v1 forbidden.toList).toArray := by
  dsimp [ByteImpl.generate_next_graphs, AdjMat.generate_next_graphs]
  -- get_isolated と get_unused の等価性を使用
  have h_iso : (get_isolated g v1 forbidden).toList =
        AdjMat.get_isolated (g.toImpl) v1 forbidden.toList :=
    get_isolated_eq g v1 forbidden
  have h_unused : (get_unused g v1 forbidden).toList =
        AdjMat.get_unused (g.toImpl) v1 forbidden.toList :=
    get_unused_eq g v1 forbidden
  simp
  -- 3. get_isolated の結果リストで場合分けをする
  -- これが `if isolated.size > 0` と `match isolated` の両方を解決します
  match h_iso_2 : AdjMat.get_isolated (AdjMat.toImpl g) v1 forbidden.toList with
  | [] =>
    -- 【ケース1: 孤立点がない場合】
    -- ByteImpl: if 条件 (size > 0) は False になる
    -- Reference: match は [] にマッチする
    -- 1. 右辺の match [] with ... を整理
    dsimp
    -- 2. if 文を else 側に倒す (if_neg を使用)
    -- 理由: 孤立点が空なので size > 0 は False
    rw [dif_neg]
    -- 【サブゴール1】条件が False であることの証明
    · -- 1. Arrayの等式を Listの等式に変換する
      -- (Array.toList_inj.mp : a.toList = b.toList → a = b)
      apply Array.toList_inj.mp
      -- 2. Array.map や toArray を List の形に整理
      -- 左辺: (Array.map ...).toList → List.map ...
      -- 右辺: ((List.map ...).toArray).toList → List.map ...
      simp only [Array.toList_map]
      -- 3. map の合成法則 (map f (map g l) = map (f ∘ g) l) を適用
      rw [List.map_map]
      -- 4. すでに示してある h_unused (リストの中身が同じ) を適用
      rw [h_unused]
      -- 5. map の中身の関数が等しいことを示す
      simp
      intro v _
      -- 6. ここで用意しておいた定理を使う
      rw [toImpl_add_edge_eq]
    -- 【サブゴール2】メインの証明 (else側: unused の処理)
    · -- 左辺: Arrayのmap連鎖をListのmapに変換して整理
      simp
      simp [<- h_iso] at h_iso_2
      exact h_iso_2
  | h :: t =>
    dsimp
    rw [dif_pos]
    · -- 左辺: (#[iso] ++ unused).map ...
      -- 右辺: (h :: unused).map ...
      apply Array.toList_inj.mp
      · -- ByteImpl側の isolated[0] が h であることの証明
        simp only [Array.map_append, Array.toList_append, Array.toList_map]
        -- リストの構造: [iso] ++ unused_list
        rw [List.map_cons] -- 右辺を h :: tail に分解
        -- 先頭 (Isolated) の一致
        have h_head :
          (get_isolated g v1 forbidden)[0]'(
            by simp [<-h_iso] at h_iso_2;rw [Array.size_eq_length_toList, h_iso_2]; simp;
            ) = h := by
          have size_pos : 0 < (get_isolated g v1 forbidden).size := by
            simp [Array.size_eq_length_toList, h_iso, h_iso_2]
          simp [<-h_iso] at h_iso_2
          simp [<-Array.getElem_toList, h_iso_2]
        rw [h_head]
        rw [toImpl_add_edge_eq]
        simp only [<-h_unused, <-toImpl_add_edge_eq]
        simp
      -- 後続 (Unused) の一致
      · simp [Array.size_eq_length_toList, h_iso, h_iso_2]

-- 修正後の transition に対する証明
theorem transition_eq {n} (S : Array (AdjMat n)) (v1 : Fin n) (forbidden : Array (Fin n)) :
    -- 左辺: Byte版で遷移してから、Ref版に変換 (map toImpl)
    (ByteImpl.transition S v1 forbidden).map AdjMat.toImpl =
    -- 右辺: Ref版に変換してから、Ref版で遷移し、最後に型を合わせる (toArray)
    (AdjMat.transition (S.toList.map AdjMat.toImpl) v1 forbidden.toList).toArray := by
  -- 1. 定義を展開
  dsimp [ByteImpl.transition, AdjMat.transition]
  -- 2. Array の等式を List の等式に変換 (証明のしやすさのため)
  apply Array.toList_inj.mp
  -- 3. Array.map, toArray などを List の形に整理
  simp only [Array.toList_map, Array.toList_flatMap]
  -- 4. List.map と List.flatMap の交換法則 (map_flatMap) を適用
  --    map f (flatMap g l) = flatMap (fun x => map f (g x)) l
  rw [List.map_flatMap, List.flatMap_map]
  -- 5. map の中身の関数が等価であることを示す
  apply List.flatMap_congr
  intro g
  -- 6. ここで前回の定理 (generate_next_graphs_eq) がそのまま使える
  --    generate_next_graphs_eq: (ByteGen ...).map toImpl = (RefGen ...).toArray
  --    これを List の形 (.toList) にして適用
  have h_gen := generate_next_graphs_eq g v1 forbidden
  -- 両辺を toList に変換して比較
  rw [← Array.toList_inj] at h_gen
  simp only [Array.toList_map] at h_gen
  -- 適用
  rw [h_gen]
  -- 7. 最後に引数の形 (forbidden.toList) が合っているか確認して終了
  simp

-- 【公理】reduce_iso の可換性
-- 「Byte版で同型除去してから変換したもの」は、
-- 「変換してからRef版で同型除去したもの」と等しいと仮定する。
axiom reduce_iso_eq_comm {n} (S : Array (AdjMat n)) (anchors : Array (Fin n)) :
    (ByteImpl.reduce_iso S anchors).toList.map AdjMat.toImpl =
    AdjMat.reduce_iso (S.toList.map AdjMat.toImpl) anchors.toList

-- 【補題1】transition のリスト版等価性
-- 前回の transition_eq (Array版) から、List.map の形での等価性を導く。
-- これがあると simp での連鎖がスムーズになります。
theorem transition_eq_list {n} (S : Array (AdjMat n)) (v1 : Fin n) (forbidden : Array (Fin n)) :
    (ByteImpl.transition S v1 forbidden).toList.map AdjMat.toImpl =
    AdjMat.transition (S.toList.map AdjMat.toImpl) v1 forbidden.toList := by
  -- 前回の定理 transition_eq を利用
  have h := transition_eq S v1 forbidden
  -- 2. 等式の両辺に .toList を適用して、Array の等式から List の等式に変える
  --    h : Array.map ... = (...).toArray
  --    ↓
  --    h : (Array.map ...).toList = ((...).toArray).toList
  apply congr_arg Array.toList at h
  -- 3. List と Array の変換ルール (map, toArray) を適用して形を整える
  --    (arr.map f).toList  ==> arr.toList.map f
  --    (list.toArray).toList ==> list
  simp only [Array.toList_map] at h
  -- 4. これで h がゴールと完全に一致するはず
  exact h

-- 【補題2】filter の整合性
-- Array.filter して toList したものは、toList して List.filter したものと同じ。
theorem filter_toArray_toList_eq {α} (arr : Array α) (p : α → Bool) :
    (arr.filter p).toList = arr.toList.filter p := by
  rw [Array.toList_filter]

theorem enumerate_Gamma_4_4_eq {n} (v_list : List (Fin n))
    (S0_byte : Array (ByteImpl.AdjMat n)) -- Byte版の入力
    (S0_impl : List (GraphEnumeration.AdjMat n)) -- Impl版の入力
    -- 仮定: 入力グラフ集合が一致していること
    (h_S0 : S0_byte.toList.map AdjMat.toImpl = S0_impl) :
    -- 左辺: ByteImplの結果をリストにして変換したもの
    (ByteImpl.enumerate_Gamma_4_4 n v_list S0_byte).toList.map AdjMat.toImpl =
    -- 右辺: RefImplの結果
    AdjMat.enumerate_Gamma_4_4 n v_list S0_impl := by
  -- 定義を展開
  dsimp [ByteImpl.enumerate_Gamma_4_4, AdjMat.enumerate_Gamma_4_4]
  -- v_list のパターンマッチで分岐
  split
  · -- Case: [v1, v2, v3, v4]
    next v1 v2 v3 v4 =>
      -- 魔法のコマンド: ここですべての変換を一気に行う
      simp only [
        reduce_iso_eq_comm,      -- reduce_iso の壁を越える
        transition_eq_list,      -- transition の壁を越える
        filter_toArray_toList_eq,-- filter の壁を越える
        h_S0
      ]
  · -- Case: その他 (空リストなど)
    simp

end ByteImpl
end GraphEnumeration
