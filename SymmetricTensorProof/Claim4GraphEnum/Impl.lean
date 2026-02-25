import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Basic

namespace Claim4GraphEnum.Impl

/-
Adjacency Matrix structure for a graph with n vertices.
data[i][j] is true if there is an edge between i and j.
We include a proof that the dimensions are exactly n x n.
-/
structure AdjMat (n : Nat) where
  data : Array (Array Bool)
  h_size : data.size = n ∧ ∀ (i : Fin data.size), (data[i]).size = n

namespace AdjMat

/- Create an empty graph with n vertices. -/
def empty (n : Nat) : AdjMat n :=
  let row := Array.replicate n false
  let data := Array.replicate n row
  { data := data,
    h_size := by
      constructor
      · rw [Array.size_replicate]
      · intro i
        change (Array.replicate n (Array.replicate n false))[i].size = n
        simp [Array.getElem_replicate, Array.size_replicate]
  }

/- Safe access to the adjacency matrix. -/
def get {n} (g : AdjMat n) (u v : Fin n) : Bool :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  let col_idx : Fin row.size := ⟨v.val, by
    have h : row.size = n := g.h_size.2 row_idx
    rw [h]; exact v.isLt⟩
  row[col_idx]

/- Private helper to set a value in the matrix. -/
def set {n} (g : AdjMat n) (u v : Fin n) (b : Bool) : AdjMat n :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  let col_idx : Fin row.size := ⟨v.val, by
    have h : row.size = n := g.h_size.2 row_idx
    rw [h]; exact v.isLt⟩
  let new_row := row.set col_idx b
  let new_data := g.data.set row_idx new_row
  { data := new_data,
    h_size := by
      constructor
      · rw [Array.size_set, g.h_size.1]
      · intro i
        dsimp
        rw [Array.getElem_set]
        split
        · rw [Array.size_set]
          convert g.h_size.2 _
        · have h_sz : (g.data.set row_idx new_row).size = g.data.size := by simp [Array.size_set]
          convert g.h_size.2 ⟨i.val, h_sz ▸ i.isLt⟩
  }

/- Add an edge between u and v (symmetric). -/
def add_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v true
  g1.set v u true

/- Remove an edge between u and v (symmetric). -/
def remove_edge {n} (g : AdjMat n) (u v : Fin n) : AdjMat n :=
  let g1 := g.set u v false
  g1.set v u false

/- get と set をつなぐ lemma -/
lemma get_set_eq {n} (g : AdjMat n) (u v x y : Fin n) (b : Bool) :
    (g.set u v b).get x y = if x = u ∧ y = v then b else g.get x y := by
  simp [get, set]
  simp only [Array.getElem_set]
  by_cases h1 : u = x <;> by_cases h2 : v = y
  · subst h1; subst h2; simp
  · subst h1
    have h_ne : y ≠ v := Ne.symm h2
    simp [h_ne]
    rw [Array.getElem_set_ne (h := Fin.val_injective.ne h2)]
  · simp [Fin.val_injective.ne h1]
    intro h; subst h; contradiction
  · simp [Fin.val_injective.ne h1]
    intro h; subst h; contradiction

/- add_edge した後に get をしても整合性が保てるという lemma -/
lemma get_add_edge {n} (g : AdjMat n) (u v x y : Fin n) :
    (g.add_edge u v).get x y =
    (g.get x y || (x = u ∧ y = v) || (x = v ∧ y = u)) := by
  simp only [add_edge]
  rw [get_set_eq]
  rw [get_set_eq]
  by_cases h1 : x = v ∧ y = u
  · simp [h1]
  · by_cases h2 : x = u ∧ y = v
    · simp [h2]
    · simp [h1, h2]

/- add_edge した後に get をしても整合性が保てるという lemma (Prop 版) -/
lemma get_add_edge_Prop {n} (g : AdjMat n) (u v x y : Fin n) :
    (g.add_edge u v).get x y = true ↔
    (g.get x y = true ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)) := by
  rw [get_add_edge]
  simp [Bool.or_eq_true]
  tauto

/- Calculate the degree of a vertex u. -/
def degree {n} (g : AdjMat n) (u : Fin n) : Nat :=
  let row_idx : Fin g.data.size := ⟨u.val, by rw [g.h_size.1]; exact u.isLt⟩
  let row := g.data[row_idx]
  row.toList.foldl (fun count b => if b then count + 1 else count) 0

/- Get neighbors of a vertex -/
def neighbors {n} (g : AdjMat n) (u : Fin n) : List (Fin n) :=
  (List.finRange n).filter (fun v => g.get u v)

-- ==========================================
-- 方法1の実装: 頂点置換
-- ==========================================

/-
  Method 1: 隣接する次数3の2頂点 v1, v2 を K4 に置換する。
  Spec の `Method1_Rel` に対応。頂点数は n から n+2 に増える。
-/
def apply_method1 {n} (g : AdjMat n) : List (AdjMat (n + 2)) :=
  let deg3_nodes := (List.finRange n).filter (fun v => g.degree v == 3)
  -- 隣接する次数3のペアを見つける (重複を避けるため u < v)
  let edges := deg3_nodes.flatMap (fun u =>
    deg3_nodes.filterMap (fun v =>
      if u.val < v.val && g.get u v then some (u, v) else none
    )
  )
  edges.flatMap (fun (v1, v2) =>
    -- v1, v2 それぞれの外部の隣接頂点を取得 (Specの X1, X2 に対応)
    let X1 := (g.neighbors v1).filter (fun x => x ≠ v2)
    let X2 := (g.neighbors v2).filter (fun x => x ≠ v1)
    match X1, X2 with
    | [x1a, x1b], [x2a, x2b] =>
      -- 新しいK4の頂点に対する外部接続の割り当て方 (4パターン)
      let configs := [
        ((x1a, x1b), (x2a, x2b)),
        ((x1a, x1b), (x2b, x2a)),
        ((x1b, x1a), (x2a, x2b)),
        ((x1b, x1a), (x2b, x2a))
      ]
      configs.map (fun ((a1, b1), (a2, b2)) =>
        let cast (x : Fin n) : Fin (n + 2) := Fin.castAdd 2 x
        let u1 := cast v1
        let u2 := cast v2
        let u3 : Fin (n + 2) := ⟨n, by omega⟩     -- 新頂点 n
        let u4 : Fin (n + 2) := ⟨n + 1, by omega⟩ -- 新頂点 n+1
        let old_nodes := List.finRange n
        -- 1. 新しい空のグラフ
        let g0 := empty (n + 2)
        -- 2. 旧頂点間（v1, v2に関係ないもの）の辺をコピー
        let old_pairs := old_nodes.flatMap (fun i =>
          old_nodes.filterMap (fun j =>
            if i.val < j.val && i ≠ v1 && i ≠ v2 && j ≠ v1 && j ≠ v2 && g.get i j
            then some (i, j) else none
          )
        )
        let g1 := old_pairs.foldl (fun acc (i, j) => acc.add_edge (cast i) (cast j)) g0
        -- 3. K4 の内部結線 (u1, u2, u3, u4 は互いに全て繋がる)
        let K4 := [u1, u2, u3, u4]
        let k4_pairs := K4.flatMap (fun i =>
          K4.filterMap (fun j => if i.val < j.val then some (i, j) else none)
        )
        let g2 := k4_pairs.foldl (fun acc (i, j) => acc.add_edge i j) g1
        -- 4. 外部との接続
        let g3 := g2.add_edge u1 (cast a1)
        let g4 := g3.add_edge u3 (cast b1)
        let g5 := g4.add_edge u2 (cast a2)
        g5.add_edge u4 (cast b2)
      )
    | _, _ => [] -- 次数3の条件を満たしていればここは通らない
  )

def map_idx {n} (u1 u2 u3 u4 : Fin (n + 2)) (hn_gt_0 : n > 0) (x : Fin (n + 2)) : Fin n :=
  let u_list := [u1.val, u2.val, u3.val, u4.val]
  let less_count := u_list.countP (fun u_val => u_val < x.val)
  let raw := x.val - less_count
  ⟨raw % n, Nat.mod_lt _ hn_gt_0⟩

/-
  Method 1 Inverse: グラフ中の K4 (互いに隣接する4頂点) を見つけ、
  それを隣接する次数3の2頂点に縮約する。
  (10,0) -> (8,4) のように頂点数を n+2 から n へ減らす探索に使用する。
-/
def apply_inv_method1 {n} (g : AdjMat (n + 2)) : List (AdjMat n) :=
  -- n < 2 のときは縮約先の頂点数が足りないため空リストを返す
  if h_n : n < 2 then
    []
  else
    -- n >= 2 の証明 (インデックス計算用)
    have hn_ge_2 : n ≥ 2 := Nat.le_of_not_lt h_n
    have hn_gt_0 : n > 0 := by omega
    -- Method 1 の置換対象は次数4になっているはずなので絞り込む
    let deg4_nodes := (List.finRange (n + 2)).filter (fun v => g.degree v == 4)
    -- K4を構成する4頂点の組み合わせを探索 (重複防止のため u1 < u2 < u3 < u4)
    let k4_sets := deg4_nodes.flatMap (fun u1 =>
      deg4_nodes.flatMap (fun u2 =>
        if u1.val < u2.val && g.get u1 u2 then
          deg4_nodes.flatMap (fun u3 =>
            if u2.val < u3.val && g.get u1 u3 && g.get u2 u3 then
              deg4_nodes.filterMap (fun u4 =>
                if u3.val < u4.val && g.get u1 u4 && g.get u2 u4 && g.get u3 u4 then
                  some [u1, u2, u3, u4]
                else none
              )
            else []
          )
        else []
      )
    )
    k4_sets.flatMap (fun K4 =>
      match K4 with
      | [u1, u2, u3, u4] =>
        -- 各頂点の K4 外部の近傍を取得 (K4内で次数3を消費しているので、外部近傍は1つのはず)
        let ext_neighbors (u : Fin (n + 2)) : List (Fin (n + 2)) :=
          (g.neighbors u).filter (fun x => !K4.contains x)
        match ext_neighbors u1, ext_neighbors u2, ext_neighbors u3, ext_neighbors u4 with
        | [x1], [x2], [x3], [x4] =>
          -- 4頂点を2つのペア (新しい頂点 v1, v2 の元) に分ける3通りの分割
          let configs := [
            ((u1, x1, u2, x2), (u3, x3, u4, x4)),
            ((u1, x1, u3, x3), (u2, x2, u4, x4)),
            ((u1, x1, u4, x4), (u2, x2, u3, x3))
          ]
          configs.filterMap (fun ((_, xa, _, xb), (_, xc, _, xd)) =>
            -- 縮約後の新頂点 v1 に xa, xb が、v2 に xc, xd が結ばれる。
            -- xa == xb などの場合、多重辺ができてしまうため除外する。
            if xa == xb || xc == xd then none
            else
              -- 新しい2つの頂点はインデックス n-2 と n-1 を使う
              let v1 : Fin n := ⟨n - 2, by omega⟩
              let v2 : Fin n := ⟨n - 1, by omega⟩
              let old_nodes := List.finRange (n + 2)
              let g0 := empty n
              -- 1. K4 以外の旧辺をコピー
              let pairs := old_nodes.flatMap (fun i =>
                old_nodes.filterMap (fun j =>
                  if i.val < j.val && !K4.contains i && !K4.contains j && g.get i j then
                    some (i, j)
                  else none
                )
              )
              let g1 := pairs.foldl (fun acc (i, j) => acc.add_edge (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 i) (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 j)) g0
              -- 2. 新頂点 v1 と外部近傍 (xa, xb) を結ぶ
              let g2 := g1.add_edge v1 (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 xa)
              let g3 := g2.add_edge v1 (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 xb)
              -- 3. 新頂点 v2 と外部近傍 (xc, xd) を結ぶ
              let g4 := g3.add_edge v2 (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 xc)
              let g5 := g4.add_edge v2 (AdjMat.map_idx u1 u2 u3 u4 hn_gt_0 xd)
              -- 4. 新頂点 v1, v2 自身を結ぶ
              let g6 := g5.add_edge v1 v2
              some g6
          )
        | _, _, _, _ => [] -- 外部近傍がちょうど1つでない場合は K4 置換の逆操作の対象外
      | _ => []
    )

-- ==========================================
-- 方法2の実装: 辺の付加
-- ==========================================

/-
  Method 2: 互いに隣接しない次数3の2頂点間に辺を追加する。
  Spec の `Method2_Rel` に対応し、条件を満たす全ての可能な新しいグラフを返す。
-/
def apply_method2 {n} (g : AdjMat n) : List (AdjMat n) :=
  let deg3_nodes := (List.finRange n).filter (fun v => g.degree v == 3)
  -- 重複を避けるため u < v のペアのみ探索
  let pairs := deg3_nodes.flatMap (fun u =>
    deg3_nodes.filterMap (fun v =>
      if u.val < v.val && !(g.get u v) then
        some (u, v)
      else none
    )
  )
  pairs.map (fun (u, v) => g.add_edge u v)

/-
  Method 2 Inverse: 互いに隣接する次数4の2頂点間の辺を削除する。
  (10,2) -> (10,0) のように、頂点数を変えずに次数4の頂点を減らす探索に使用する。
-/
def apply_inv_method2 {n} (g : AdjMat n) : List (AdjMat n) :=
  let deg4_nodes := (List.finRange n).filter (fun v => g.degree v == 4)
  -- 隣接している次数4のペアを見つける (重複を避けるため u < v)
  let edges := deg4_nodes.flatMap (fun u =>
    deg4_nodes.filterMap (fun v =>
      if u.val < v.val && g.get u v then
        some (u, v)
      else none
    )
  )
  -- 見つかった辺を削除したグラフのリストを返す
  edges.map (fun (u, v) => g.remove_edge u v)


-- ==========================================
-- 方法3-bの実装: 頂点の分割
-- ==========================================

/- 4要素のリストを2個ずつのペア(3通り)に分割するヘルパー -/
def partitions_of_4 {α} (l : List α) : List (List α × List α) :=
  match l with
  | [a, b, c, d] => [
      ([a, b], [c, d]),
      ([a, c], [b, d]),
      ([a, d], [b, c]),
      ([c, d], [a, b]),
      ([b, d], [a, c]),
      ([b, c], [a, d])
    ]
  | _ => []

/-
  特定の頂点 w とその近傍の分割 (N1, N2) に基づいて頂点を分割する。
  Spec の `Method3b_Rel` の構成手順と完全に一致する実装。
-/
def split_vertex {n} (g : AdjMat n) (w : Fin n) (N1 N2 : List (Fin n)) : AdjMat (n + 1) :=
  let cast (x : Fin n) : Fin (n + 1) := Fin.castSucc x
  let v1 : Fin (n + 1) := cast w
  let v2 : Fin (n + 1) := Fin.last n
  let old_nodes := List.finRange n
  -- 1. 新しい空のグラフからスタート
  let g0 := empty (n + 1)
  -- 2. 旧頂点間の辺（wに関係ないもの）をコピー
  let pairs := old_nodes.flatMap (fun i =>
    old_nodes.filterMap (fun j =>
      if i.val < j.val && i != w && j != w && g.get i j then some (i, j) else none
    )
  )
  let g1 := pairs.foldl (fun acc (i, j) => acc.add_edge (cast i) (cast j)) g0
  -- 3. w (v1) と N1 の間に辺を張る
  let g2 := N1.foldl (fun acc x => acc.add_edge v1 (cast x)) g1
  -- 4. 新頂点 (v2) と N2 の間に辺を張る
  let g3 := N2.foldl (fun acc x => acc.add_edge v2 (cast x)) g2
  -- 5. v1 と v2 の間に辺を張る
  g3.add_edge v1 v2

/-
  Method 3-b: 次数4のすべての頂点について、考えうるすべての分割パターンを生成する。
-/
def apply_method3b {n} (g : AdjMat n) : List (AdjMat (n + 1)) :=
  let deg4_nodes := (List.finRange n).filter (fun w => g.degree w == 4)
  deg4_nodes.flatMap (fun w =>
    let ns := g.neighbors w
    let parts := partitions_of_4 ns
    parts.map (fun (N1, N2) => split_vertex g w N1 N2)
  )


-- ==========================================
-- 方法3-bの逆操作: 辺の縮約 (Edge Contraction)
-- ==========================================

/-
  Method 3-b Inverse: 隣接する次数3の2頂点を縮約し、1つの次数4の頂点にする。
  (10,0) -> (8,1) のように頂点数を n+1 から n へ減らす探索に使用する。
-/
def apply_inv_method3b {n} (g : AdjMat (n + 1)) : List (AdjMat n) :=
  -- n = 0 のときは縮約先がないため空リストを返す
  if h_n : n = 0 then
    []
  else
    -- n > 0 の証明 (配列のインデックス計算の安全性のため)
    have hn_gt_0 : n > 0 := Nat.pos_of_ne_zero h_n
    -- 次数3の頂点をすべて取得
    let deg3_nodes := (List.finRange (n + 1)).filter (fun v => g.degree v == 3)
    -- 隣接している次数3のペア (u, v) を列挙 (重複防止のため u < v)
    let edges := deg3_nodes.flatMap (fun u =>
      deg3_nodes.filterMap (fun v =>
        if u.val < v.val && g.get u v then some (u, v) else none
      )
    )
    edges.filterMap (fun (u, v) =>
      -- それぞれの「相手以外の隣接頂点」を取得 (サイズは共に2)
      let N_u := (g.neighbors u).filter (fun x => x != v)
      let N_v := (g.neighbors v).filter (fun x => x != u)
      -- 共通の隣接頂点を持つ場合は、縮約すると多重辺ができるためスキップ
      let shared := N_u.any (fun x => N_v.contains x)
      if shared then none
      else
        -- u と v を新しい頂点 (インデックス n-1) に統合し、他の頂点は間を詰めるマッピング
        let map_idx (x : Fin (n + 1)) : Fin n :=
          let raw :=
            if x == u || x == v then n - 1
            else if x.val < u.val then x.val
            else if x.val < v.val then x.val - 1
            else x.val - 2
          -- raw は論理的に必ず n 未満になるため、% n を使ってLeanの境界証明を簡略化
          ⟨raw % n, Nat.mod_lt _ hn_gt_0⟩
        let old_nodes := List.finRange (n + 1)
        -- 1. n頂点の新しい空グラフを用意
        let g0 := empty n
        -- 2. u, v に接続していない旧辺をコピー
        let pairs := old_nodes.flatMap (fun i =>
          old_nodes.filterMap (fun j =>
            if i.val < j.val && i != u && i != v && j != u && j != v && g.get i j then
              some (i, j)
            else none
          )
        )
        let g1 := pairs.foldl (fun acc (i, j) => acc.add_edge (map_idx i) (map_idx j)) g0
        -- 3. u の元の隣接頂点と、新しい統合頂点 (n-1) を結ぶ
        let g2 := N_u.foldl (fun acc x => acc.add_edge (map_idx u) (map_idx x)) g1
        -- 4. v の元の隣接頂点と、新しい統合頂点 (n-1) を結ぶ
        let g3 := N_v.foldl (fun acc x => acc.add_edge (map_idx v) (map_idx x)) g2
        some g3
    )


-- ==========================================
-- Isomorphism Reduction (同型除去)
-- ==========================================

/-
  同型判定による重複排除関数。
  Correctness証明時には中身を見ずにすむよう opaque にしておく。
  （実行時には Nauty や独自の実装に差し替える）-/
opaque reduce_iso {n} (S : List (AdjMat n)) : List (AdjMat n)

/- リスト全体のグラフに対して Method 1 を適用し、同型を除去する -/
def step_method1 {n} (S : List (AdjMat n)) : List (AdjMat (n + 2)) :=
  reduce_iso (S.flatMap apply_method1)

/- リスト全体のグラフに対して Method 1 の逆操作を適用し、同型を除去する -/
def step_inv_method1 {n} (S : List (AdjMat (n + 2))) : List (AdjMat n) :=
  reduce_iso (S.flatMap apply_inv_method1)

/- リスト全体のグラフに対して Method 2 を適用し、同型を除去する -/
def step_method2 {n} (S : List (AdjMat n)) : List (AdjMat n) :=
  reduce_iso (S.flatMap apply_method2)

/- リスト全体のグラフに対して Method 2 の逆操作を適用し、同型を除去する -/
def step_inv_method2 {n} (S : List (AdjMat n)) : List (AdjMat n) :=
  reduce_iso (S.flatMap apply_inv_method2)

/- リスト全体のグラフに対して Method 3-b を適用し、同型を除去する -/
def step_method3b {n} (S : List (AdjMat n)) : List (AdjMat (n + 1)) :=
  reduce_iso (S.flatMap apply_method3b)

/- リスト全体のグラフに対して Method 3-b の逆操作を適用し、同型を除去する -/
def step_inv_method3b {n} (S : List (AdjMat (n + 1))) : List (AdjMat n) :=
  reduce_iso (S.flatMap apply_inv_method3b)

end AdjMat
end Claim4GraphEnum.Impl
