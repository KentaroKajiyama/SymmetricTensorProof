import Mathlib

lemma array_foldl_test (a : Array Bool) :
  a.foldl (fun c b => if b then c+1 else c) 0 = (a.toList.map (fun b => if b then 1 else 0)).sum := by
  -- try to find the lemma
  simp [Array.foldl_eq_foldl_data] -- check if error
