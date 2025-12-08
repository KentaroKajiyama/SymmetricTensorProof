import SymmetricTensorProof.check
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Sym.Sym2

open VerifyIndependence

-- Concrete Params to avoid noncomputable sorry
def P_small : Params := { n := 5, t := 2, ht₁ := by decide, ht₂ := by decide }
def P_large : Params := { n := 10, t := 3, ht₁ := by decide, ht₂ := by decide }

-- Simple LCG for random ZMod p
structure LcRNG where
  state : UInt64

def lcg_next (rng : LcRNG) : UInt64 × LcRNG :=
  let new_state := rng.state * 0x5851f42d4c957f2d + 0x14057b7ef767814f
  (new_state, { state := new_state })

def get_random_Zp {p : ℕ} (rng : LcRNG) : ZMod p × LcRNG :=
  let (val, rng') := lcg_next rng
  let val_zmod : ZMod p := (val.toNat % p : ℕ)
  (val_zmod, rng')

def generate_assignment
    (P : Params) (seed : ℕ) {p : ℕ} [Fact p.Prime]
    : Fin P.n → Fin P.t → ZMod p :=
  let rng_initial : LcRNG := { state := UInt64.ofNat seed }
  let (values, _) := (List.range P.n).foldl (fun (acc_outer, rng_outer) _ =>
    let (row_vals, rng_inner) := (List.range P.t).foldl (fun (acc_inner, rng_curr) _ =>
      let (val, rng_next) := get_random_Zp (p := p) rng_curr
      (acc_inner.push val, rng_next)
    ) (#[], rng_outer)
    (acc_outer.push row_vals, rng_inner)
  ) ((#[] : Array (Array (ZMod p))), rng_initial)
  fun i j => (values[i]!)[j]!



def p_val : ℕ := 17
instance : Fact p_val.Prime := fact_iff.mpr (by decide)

def main : IO Unit := do
  let n := 5
  let t := 2
  let p := p_val
  let P := P_small
  have : Fact p.Prime := fact_iff.mpr (by decide)

  -- Assignment with random seed
  let assignment := generate_assignment P 12345 (p := p)

  IO.println s!"Testing check_independence with n={n}, t={t}, p={p} (d_col = {t*(t+1)/2})"

  -- Case 1: Empty Graph
  let G_empty : Graph P := ∅
  let res_empty := check_independence P G_empty assignment
  IO.println s!"[1] Empty Graph: {res_empty} (Expected: true)"

  -- Case 2: Single Edge (0, 1)
  let u : Fin n := 0
  let v : Fin n := 1
  let h_u : u < n := by decide
  let h_v : v < n := by decide
  let e1 : Ground P := Sym2.mk (⟨u, h_u⟩, ⟨v, h_v⟩)
  let G_single : Graph P := {e1}
  let res_single := check_independence P G_single assignment
  IO.println s!"[2] Single Edge ({u}, {v}): {res_single} (Expected: true)"

  -- Case 3: 3 Edges (should be independent if random enough)
  -- Edges: (0,1), (1,2), (2,3)
  let e2 := Sym2.mk ((⟨1, by decide⟩ : Fin n), (⟨2, by decide⟩ : Fin n))
  let e3 := Sym2.mk ((⟨2, by decide⟩ : Fin n), (⟨3, by decide⟩ : Fin n))
  let G_3 : Graph P := {e1, e2, e3}
  let res_3 := check_independence P G_3 assignment
  IO.println s!"[3] 3 Edges: {res_3} (Expected: true)"

  -- Case 4: 4 Edges (Must be dependent because d_col = 3)
  -- Edges: (0,1), (1,2), (2,3), (3,4)
  let e4 := Sym2.mk ((⟨3, by decide⟩ : Fin n), (⟨4, by decide⟩ : Fin n))
  let G_4 : Graph P := {e1, e2, e3, e4}
  let res_4 := check_independence P G_4 assignment
  IO.println s!"[4] 4 Edges: {res_4} (Expected: false)"

  -- Dependent Triangle (maybe? usually independent in generic, but let's test specific dependency if we knew one)
  -- The core logic is Rank(M) == |Edges|.
  -- If |Edges| > d_col, it returns false.

  if res_empty && res_single && res_3 && !res_4 then
     IO.println "SMALL TESTS PASSED"
  else
     IO.println "SOME SMALL TESTS FAILED"

  -- Case 5: Larger Graph n=10, t=3
  -- d_col = t*(t+1)/2 = 3*4/2 = 6
  let n_large := 10
  let t_large := 3
  let P_large := P_large
  IO.println s!"Testing check_independence with n={n_large}, t={t_large}, p={p} (d_col = {6})"

  let assignment_large := generate_assignment P_large 67890 (p := p)

  -- 6 edges (Expected: True if independent)
  -- select 6 distinct edges
  let edges_6 : List (Ground P_large) := [
    Sym2.mk (⟨0, by decide⟩, ⟨1, by decide⟩),
    Sym2.mk (⟨1, by decide⟩, ⟨2, by decide⟩),
    Sym2.mk (⟨2, by decide⟩, ⟨3, by decide⟩),
    Sym2.mk (⟨3, by decide⟩, ⟨4, by decide⟩),
    Sym2.mk (⟨4, by decide⟩, ⟨5, by decide⟩),
    Sym2.mk (⟨5, by decide⟩, ⟨6, by decide⟩)
  ]
  let G_6 : Graph P_large := edges_6.toFinset
  let res_6 := check_independence P_large G_6 assignment_large
  IO.println s!"[5-1] 6 Edges: {res_6} (Expected: true)"

  -- 7 edges (Expected: False because 7 > 6)
  let edges_7 := Sym2.mk ((⟨6, by decide⟩ : Fin n_large), (⟨7, by decide⟩ : Fin n_large)) :: edges_6
  let G_7 : Graph P_large := edges_7.toFinset
  let res_7 := check_independence P_large G_7 assignment_large
  IO.println s!"[5-2] 7 Edges: {res_7} (Expected: false)"

  if res_6 && !res_7 then
     IO.println "LARGE TESTS PASSED"
  else
     IO.println "SOME LARGE TESTS FAILED"
