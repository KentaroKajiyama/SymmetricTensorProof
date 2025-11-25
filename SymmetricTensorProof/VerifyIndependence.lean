import SymmetricTensorProof.MatroidDefinition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Algebra.MvPolynomial.Basic

open MvPolynomial

/--
Evaluates the symmetric tensor matrix at a given integer assignment.
The result is a matrix over ℚ.
-/
def evalMatrix (V d : ℕ) (edges : List (Fin V × Fin V)) (assignment : Vars V d → ℤ) :
    Matrix (Fin (d * d)) (Fin edges.length) ℚ :=
  let P := symmetricTensorMatrix V d edges
  -- Lift the integer assignment to ℚ
  let assignmentQ : Vars V d → ℚ := fun v => (assignment v : ℚ)
  -- Apply evaluation to each entry of the matrix
  Matrix.map P (fun p => aeval assignmentQ p)

/--
Computes the rank of a matrix over ℚ.
TODO: Connect this to the Gaussian elimination implementation in check.lean
-/
def computeRank {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : ℕ := sorry

/--
Checks if the set of edges is independent in the Symmetric Tensor Matroid
given a specific integer assignment to the variables.
Returns true if rank equals the number of edges.
-/
def check_independence (V d : ℕ) (edges : List (Fin V × Fin V)) (assignment : Vars V d → ℤ) : Bool :=
  let M := evalMatrix V d edges assignment
  let r := computeRank M
  r == edges.length
