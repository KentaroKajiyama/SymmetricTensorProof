import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Fin.Basic

open MvPolynomial

/--
Variables for the polynomial ring.
Represented as a pair (vertex, dimension_index).
-/
abbrev Vars (V d : ℕ) := Fin V × Fin d

/--
Polynomial ring over ℚ with variables `Vars V d`.
-/
abbrev Poly (V d : ℕ) := MvPolynomial (Vars V d) ℚ

/--
The symmetric tensor entry polynomial for edge (u, v) and indices (k, l).
P_{(u,v), (k,l)} = x_{u,k} * x_{v,l} + x_{v,k} * x_{u,l}
-/
def symmetricTensorEntry {V d : ℕ} (u v : Fin V) (k l : Fin d) : Poly V d :=
  X (u, k) * X (v, l) + X (v, k) * X (u, l)

/--
Constructs the Symmetric Tensor Matrix.
Rows: d * d (indexed by Fin (d * d))
Cols: edges.length (indexed by Fin edges.length)
-/
def symmetricTensorMatrix (V d : ℕ) (edges : List (Fin V × Fin V)) :
    Matrix (Fin (d * d)) (Fin edges.length) (Poly V d) :=
  fun row col =>
    let k := row / d
    let l := row % d
    let (u, v) := edges.get col
    symmetricTensorEntry u v k l
