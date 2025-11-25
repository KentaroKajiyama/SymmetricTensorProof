import SymmetricTensorProof.JsonTypes
import SymmetricTensorProof.VerifyIndependence
import SymmetricTensorProof.VerifyDependence
import SymmetricTensorProof.VerifyStructure
import Lean.Data.Json

open Lean

/--
Helper to convert a Nat to Fin n, returning None if out of bounds.
-/
def toFin (k : Nat) (n : Nat) : Option (Fin n) :=
  if h : k < n then some (Fin.mk k h) else none

/--
Converts a list of edges with Nat indices to Fin V indices.
-/
def convertEdges (V : Nat) (edges : List (Nat × Nat)) : Option (List (Fin V × Fin V)) :=
  edges.mapM fun (u, v) => do
    let u' <- toFin u V
    let v' <- toFin v V
    return (u', v')

/--
Converts a flat list of integers to an assignment function (Fin V × Fin d → ℤ).
Assumes row-major ordering: index = i * d + j.
-/
def listToAssignment (V d : Nat) (l : List Int) : (Fin V × Fin d) → ℤ :=
  fun (i, j) =>
    let idx := i.val * d + j.val
    if h : idx < l.length then l.get ⟨idx, h⟩ else 0

/--
Converts the raw kernel data to SerializedPoly.
-/
def convertKernel (V d : Nat) (k : List (List (Int × List ((Nat × Nat) × Nat)))) : Option (List (SerializedPoly V d)) :=
  k.mapM fun poly =>
    poly.mapM fun (coeff, terms) => do
      let terms' <- terms.mapM fun ((v_idx, d_idx), exp) => do
        let v' <- toFin v_idx V
        let d' <- toFin d_idx d
        return ((v', d'), exp)
      return (coeff : ℚ, terms')

/--
Appends an error message to the error log file.
-/
def logError (id : String) (msg : String) : IO Unit := do
  let entry := s!"Graph {id}: {msg}\n"
  IO.FS.withFile "error_log.txt" IO.FS.Mode.append fun h =>
    h.putStr entry

/--
Processes a single certificate.
-/
def processGraph (c : Certificate) : IO Unit := do
  let edgesOpt := convertEdges c.V c.edges
  match edgesOpt with
  | none => logError c.id "Invalid edge indices (out of bounds)"
  | some edgesFin =>
    match c.type with
    | "i" =>
      if let some assign := c.assignment then
        let assignFn := listToAssignment c.V c.d assign
        if VerifyIndependence.check_independence c.V c.d edgesFin assignFn then
          -- IO.println s!"Graph {c.id}: Independent (Verified)"
          pure ()
        else
          logError c.id "Independence check failed"
      else
        logError c.id "Missing assignment for independence check"

    | "d" =>
      if let some k := c.kernel then
        match convertKernel c.V c.d k with
        | some kernelData =>
          if VerifyDependence.check_dependence c.V c.d edgesFin kernelData then
            -- IO.println s!"Graph {c.id}: Dependent (Verified)"
            pure ()
          else
            logError c.id "Dependence check failed"
        | none => logError c.id "Invalid kernel indices"
      else
        logError c.id "Missing kernel for dependence check"

    | _ =>
      if let some s := c.structure_analysis then
        if s.is_counter then
          if VerifyStructure.check_counterexample c.V c.d edgesFin s then
            -- IO.println s!"Graph {c.id}: Counterexample (Verified)"
            pure ()
          else
            logError c.id "Counterexample check failed"
        else
          logError c.id "Structure analysis indicates not a counterexample, but type is unknown"
      else
        logError c.id s!"Unknown type '{c.type}' and no structure analysis"

/--
Reads the stream from zcat and processes each line.
-/
partial def readStream (stdout : IO.FS.Stream) : IO Unit := do
  let line <- stdout.getLine
  if line.isEmpty then
    pure ()
  else
    match Json.parse line with
    | Except.ok json =>
      match fromJson? json with
      | Except.ok (cert : Certificate) =>
        processGraph cert
      | Except.error e =>
        IO.eprintln s!"JSON decode error: {e}"
    | Except.error e =>
      IO.eprintln s!"JSON parse error: {e}"
    readStream stdout

/--
Batch verification entry point.
-/
def verifyBatch (filename : String) : IO Unit := do
  IO.println s!"Verifying {filename}..."
  try
    let child <- IO.Process.spawn {
      cmd := "zcat",
      args := #[filename],
      stdout := IO.Process.Stdio.piped,
      stdin := IO.Process.Stdio.null
    }
    readStream child.stdout
    let _ <- child.wait
    IO.println "Verification complete."
  catch e =>
    IO.eprintln s!"Error running zcat: {e}"

def main (args : List String) : IO Unit := do
  match args with
  | [filename] => verifyBatch filename
  | _ => IO.println "Usage: Main <file.jsonl.gz>"
