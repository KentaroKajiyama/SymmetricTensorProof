import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basic
-- import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finsupp.Basic
-- import MatroidDefinition.lean

open MvPolynomial

/--
Serialized representation of a polynomial.
A list of terms, where each term is a pair of a coefficient and a list of variable powers.
The list of variable powers is a list of pairs (variable, exponent).
-/
abbrev SerializedPoly (V d : ℕ) := List (ℚ × List (Vars V d × ℕ))

/--
Deserializes a `SerializedPoly` into a `MvPolynomial`.
-/
def deserializePoly {V d : ℕ} (s : SerializedPoly V d) : Poly V d :=
  s.foldl (fun acc (coeff, vars) =>
    let exponents : Vars V d →₀ ℕ := vars.foldl (fun e (v, n) => e + Finsupp.single v n) 0
    acc + monomial exponents coeff
  ) 0

/--
Checks if the given kernel vector is a valid dependence for the symmetric tensor matroid of the graph.
Returns true if:
1. The dimensions match.
2. M * c = 0 (the vector is in the kernel).
3. c != 0 (the vector is non-zero).
-/
def check_dependence {V d : ℕ} (edges : List (Fin V × Fin V)) (kernel_data : List (SerializedPoly V d)) : Bool :=
  if h_dim : kernel_data.length = edges.length then
    let c : Fin edges.length → Poly V d := fun i =>
      deserializePoly (kernel_data.get (i.cast h_dim.symm))

    let M := symmetricTensorMatrix V d edges
    let res := Matrix.mulVec M c

    let is_kernel := ∀ i, res i = 0
    let is_nonzero := ∃ i, c i ≠ 0

    -- Since MvPolynomial over ℚ has DecidableEq, we can decide equality.
    -- However, for Bool return, we need to use decide or similar if we want to be purely boolean,
    -- or just rely on the fact that we are in a computational context (though MvPolynomial equality might be expensive).
    -- MvPolynomial ℚ has decidable equality.

    (decide is_kernel) && (decide is_nonzero)
  else
    false

-- Simple tests
section Test

  -- 2 vertices, dimension 2
  -- Variables: x_{0,0}, x_{0,1}, x_{1,0}, x_{1,1}
  -- Edge (0, 1)
  -- Matrix column for (0, 1):
  -- Row (0,0) -> k=0, l=0: x_{0,0}x_{1,0} + x_{1,0}x_{0,0} = 2 x_{0,0}x_{1,0}
  -- ...

  -- Let's just test deserialization first
  def p1_data : SerializedPoly 2 2 := [(3, [((0, 0), 2), ((1, 1), 1)])]
  -- 3 * x_{0,0}^2 * x_{1,1}^1
  def p1 : Poly 2 2 := deserializePoly p1_data

  #eval p1.coeff (Finsupp.single (0,0) 2 + Finsupp.single (1,1) 1) -- Should be 3
  #eval p1.coeff 0 -- Should be 0

end Test
