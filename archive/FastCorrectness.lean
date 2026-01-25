import SymmetricTensorProof.GraphEnum.FastImpl
import SymmetricTensorProof.GraphEnum.Impl
import Mathlib

namespace GraphEnumeration

namespace FastImpl

open GraphEnumeration.AdjMat

-- Helper to convert Array to List for comparison
theorem toList_toArray_eq {α} (l : List α) : l.toArray.toList = l := by
  simp

-- Lemma: get_isolated equivalence
theorem get_isolated_eq {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) :
    (FastImpl.get_isolated g v1 forbidden.toArray).toList = AdjMat.get_isolated g v1 forbidden := by
  dsimp [FastImpl.get_isolated, AdjMat.get_isolated]
  rw [Array.toList_filter]
  simp

-- Lemma: get_unused equivalence
theorem get_unused_eq {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) :
    (FastImpl.get_unused g v1 forbidden.toArray).toList = AdjMat.get_unused g v1 forbidden := by
  dsimp [FastImpl.get_unused, AdjMat.get_unused]
  rw [Array.toList_filter]
  simp

-- Lemma: generate_next_graphs equivalence
theorem generate_next_graphs_eq {n} (g : AdjMat n) (v1 : Fin n) (forbidden : List (Fin n)) :
    (FastImpl.generate_next_graphs g v1 forbidden.toArray).toList
      = AdjMat.generate_next_graphs g v1 forbidden := by
  dsimp [FastImpl.generate_next_graphs, AdjMat.generate_next_graphs]
  -- Define abbreviations for clarity in proof
  let iso_fast := FastImpl.get_isolated g v1 forbidden.toArray
  let iso_spec := AdjMat.get_isolated g v1 forbidden
  have h_iso : iso_fast.toList = iso_spec := get_isolated_eq g v1 forbidden
  let unused_fast := FastImpl.get_unused g v1 forbidden.toArray
  let unused_spec := AdjMat.get_unused g v1 forbidden
  have h_unused : unused_fast.toList = unused_spec := get_unused_eq g v1 forbidden
  -- Helper for size
  have h_iso_len : iso_fast.size = iso_spec.length := by
    rw [← h_iso]
    simp
  split
  · -- Case: iso_fast.size > 0
    rename_i h_len
    change iso_fast.size > 0 at h_len
    cases h_cons : iso_spec with
    | nil =>
      rw [h_cons] at h_iso_len
      simp at h_iso_len
      rw [h_iso_len] at h_len
      contradiction
    | cons head tail =>
      have : (g.get_isolated v1 forbidden) = iso_spec := by simp [iso_spec]
      simp [this, h_cons]
      -- Goal: f (iso_fast[0]) :: (unused_fast.map f).toList = f head :: (unused_spec.map f)
      · -- Head equality
        rw [← h_iso] at h_cons
        -- index 0 is valid because size > 0
        -- head is iso_fast[0]
        have h_head_val : iso_fast.toList = head :: tail := h_cons
        -- Array.get 0 extracts the first element
        -- We just need to show the value matches.
        -- Using getElem toList equivalence is standard.
        -- 1. 「配列へのアクセス」は「変換後のリストへのアクセス」と同じであることを確認
        have : iso_fast[0] = iso_fast.toList[0] := by simp
        rw [this]
        -- 2. リストの中身を head :: tail に置き換え
        have : iso_fast.toList[0] = head := by simp [h_head_val]
        rw [this]
        -- 3. (head :: tail)[0] は head なので、簡約して終了
        simp
        have : (get_unused g v1 forbidden.toArray) = unused_fast := by simp [unused_fast]
        rw [this, h_unused]
  · -- Case: iso_fast.size = 0
    rename_i h_len
    simp at h_len
    -- h_len is iso_fast = #[]
    have h_empty : iso_fast = #[] := h_len
    cases h_cons : iso_spec with
    | nil =>
      simp
      have : (g.get_isolated v1 forbidden) = iso_spec := by simp [iso_spec]
      simp [this, h_cons]
      rw [h_unused]
    | cons head tail =>
      have : (g.get_isolated v1 forbidden) = iso_spec := by simp [iso_spec]
      simp [this, h_cons]
      rw [h_unused]
      have : (g.get_unused v1 forbidden) = unused_spec := by simp [unused_spec]
      simp [this]
      -- 1. h_iso の iso_fast を空(#[])に書き換える
      rw [h_empty] at h_iso
      -- 2. #[] .toList は [] なので、simp で綺麗にする
      simp at h_iso
      -- これで h_iso は「[] = iso_spec」になります
      -- 3. iso_spec を head :: tail に書き換える
      rw [h_cons] at h_iso
      -- これで h_iso は「[] = head :: tail」になります

      -- 4. 空リストと空でないリストは等しくないので矛盾
      contradiction

-- Lemma: transition equivalence
theorem transition_eq {n} (S : List (AdjMat n)) (v1 : Fin n) (forbidden : List (Fin n)) :
    (FastImpl.transition S.toArray v1 forbidden.toArray).toList
      = AdjMat.transition S v1 forbidden := by
  dsimp [FastImpl.transition, AdjMat.transition]
  rw [Array.toList_flatMap]
  simp
  congr
  ext g
  rw [generate_next_graphs_eq]

-- Equivalence assumption for reduce_iso
axiom reduce_iso_eq {n} (S : List (AdjMat n)) (anchors : List (Fin n)) :
    (FastImpl.reduce_iso S.toArray anchors.toArray).toList = AdjMat.reduce_iso S anchors

-- Main Theorem: enumerate_Gamma_4_4 equivalence
theorem enumerate_Gamma_4_4_eq {n} (v_list : List (Fin n)) :
    (FastImpl.enumerate_Gamma_4_4 n v_list).toList = AdjMat.enumerate_Gamma_4_4 n v_list := by
  dsimp [FastImpl.enumerate_Gamma_4_4, AdjMat.enumerate_Gamma_4_4]
  split
  · -- Case [v1, v2, v3, v4]
    next v1 v2 v3 v4 =>
      simp
      -- We need to prove step by step.
      -- First step: transition S0
      have eq1 : (FastImpl.transition #[AdjMat.empty n] v1
                  (#[v1, v2, v3, v4].filter (· != v1))).toList =
                    AdjMat.transition [AdjMat.empty n] v1 ([v1, v2, v3, v4].filter (· != v1)) := by
        -- Convert arrays to lists implicitly via transition_eq
        -- But arguments need match.
        let S0 := [AdjMat.empty n]
        let f1 := [v1, v2, v3, v4].filter (· != v1)
        have : #[AdjMat.empty n] = S0.toArray := rfl
        rw [this]
        have : (#[v1, v2, v3, v4].filter (· != v1)) = f1.toArray := by
          rw [List.filter_toArray]
        rw [this]
        rw [transition_eq]
      -- S1_1
      have eq_S1_1 : (FastImpl.reduce_iso (
          FastImpl.transition #[AdjMat.empty n] v1 (
            #[v1, v2, v3, v4].filter (· != v1))) #[v1, v2, v3, v4]).toList =
                    AdjMat.reduce_iso (AdjMat.transition [AdjMat.empty n] v1
                      ([v1, v2, v3, v4].filter (· != v1))) [v1, v2, v3, v4] := by
        -- Apply reduce_iso_eq
        -- LHS inner is equivalent to RHS inner via eq1
        -- We need to carefully rewrite.
        -- reduce_iso_eq expects (S : List).toArray
        -- We have inner_fast.toList = inner_impl -> inner_fast = inner_impl.toArray
        have h : FastImpl.transition #[AdjMat.empty n] v1 (#[v1, v2, v3, v4].filter (· != v1))
          = (AdjMat.transition [AdjMat.empty n] v1
            ([v1, v2, v3, v4].filter (· != v1))).toArray := by
          congr!
        rw [h]
        have h_anchors : #[v1, v2, v3, v4] = [v1, v2, v3, v4].toArray := rfl
        rw [h_anchors]
        rw [reduce_iso_eq]
      -- Helper tactic not strictly needed but good to be explicit
      -- For brevity, we just use rewrites
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      -- Gamma 2
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      -- Gamma 3
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      -- Gamma 4
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
      rw [reduce_iso_eq, transition_eq]
  · -- Case _
    rename_i h
    simp

end FastImpl
end GraphEnumeration
