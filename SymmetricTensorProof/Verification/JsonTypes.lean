import Lean
import SymmetricTensorProof.VerifyDependence
import SymmetricTensorProof.VerifyStructure

open Lean

-- Implement FromJson for StructureAnalysis
instance : FromJson StructureAnalysis where
  fromJson? j := do
    let is_counter <- (j.getObjVal? "is_counter").bind fromJson?
    return { is_counter := is_counter }

/--
Certificate structure matching the JSON input.
Keys are mapped from short names (t, a, k, s) to readable names.
-/
structure Certificate where
  id : String
  type : String
  assignment : Option (List Int)
  /--
  Kernel data.
  Expected structure: List of polynomials.
  Each polynomial is a List of terms.
  Each term is (coefficient, List of variable powers).
  Variable power is ((vertex_idx, dim_idx), exponent).
  -/
  kernel : Option (List (List (Int × List ((Nat × Nat) × Nat))))
  structure_analysis : Option StructureAnalysis
  V : Nat
  d : Nat
  edges : List (Nat × Nat)
  deriving Inhabited

instance : FromJson Certificate where
  fromJson? j := do
    let id <- (j.getObjVal? "id").bind fromJson?
    let t <- (j.getObjVal? "t").bind fromJson?
    let a <- j.getObjValAs? (Option (List Int)) "a"
    let k <- j.getObjValAs? (Option (List (List (Int × List ((Nat × Nat) × Nat))))) "k"
    let s <- j.getObjValAs? (Option StructureAnalysis) "s"
    let V <- (j.getObjVal? "V").bind fromJson?
    let d <- (j.getObjVal? "d").bind fromJson?
    let edges <- (j.getObjVal? "edges").bind fromJson?
    return {
      id := id,
      type := t,
      assignment := a,
      kernel := k,
      structure_analysis := s,
      V := V,
      d := d,
      edges := edges
    }
