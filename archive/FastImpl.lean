import Mathlib
import SymmetricTensorProof.GraphEnum.Impl

namespace GraphEnumeration
namespace FastImpl

open GraphEnumeration.AdjMat

/-
  Fast implementation using Arrays.
-/

def get_isolated {n} (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (Fin n) :=
  let all_vertices := (List.finRange n).toArray
  all_vertices.filter (fun v => g.degree v == 0 && !(v == v1) && !forbidden.contains v)

def get_unused {n} (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (Fin n) :=
  let all_vertices := (List.finRange n).toArray
  all_vertices.filter (fun v =>
    let deg := g.degree v
    decide (1 <= deg) && decide (deg <= 3) && !g.get v1 v && !(v == v1) && !forbidden.contains v
  )

def generate_next_graphs {n}
  (g : AdjMat n) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (AdjMat n) :=
  let isolated := get_isolated g v1 forbidden
  let unused := get_unused g v1 forbidden
  let candidates :=
    if h : isolated.size > 0 then
      -- Pick ONLY the first one (since they are symmetric) and append unused
      #[isolated[0]'h] ++ unused
    else
      unused
  candidates.map (fun v => g.add_edge v1 v)

def transition {n}
  (S : Array (AdjMat n)) (v1 : Fin n) (forbidden : Array (Fin n)) : Array (AdjMat n) :=
  S.flatMap (fun g => generate_next_graphs g v1 forbidden)

opaque reduce_iso {n} (S : Array (AdjMat n)) (anchors : Array (Fin n)) : Array (AdjMat n)

def enumerate_Gamma_4_4 (n : Nat) (v_list : List (Fin n)) : Array (AdjMat n) :=
  match v_list with
  | [v1, v2, v3, v4] =>
    -- Base case: Empty graph
    let S0 := #[AdjMat.empty n]
    let all_anchors := #[v1, v2, v3, v4]
    let forbidden_for (v : Fin n) := all_anchors.filter (· != v)
    -- Gamma_1 steps (Add 3 edges to v1)
    let f1 := forbidden_for v1
    let S1_1 := reduce_iso (transition S0   v1 f1) all_anchors
    let S1_2 := reduce_iso (transition S1_1 v1 f1) all_anchors
    let S1_3 := reduce_iso (transition S1_2 v1 f1) all_anchors
    -- Gamma_2 steps (Add 3 edges to v2)
    let f2 := forbidden_for v2
    let S2_1 := reduce_iso (transition S1_3 v2 f2) all_anchors
    let S2_2 := reduce_iso (transition S2_1 v2 f2) all_anchors
    let S2_3 := reduce_iso (transition S2_2 v2 f2) all_anchors
    -- Gamma_3 steps (Add 4 edges to v3)
    let f3 := forbidden_for v3
    let S3_1 := reduce_iso (transition S2_3 v3 f3) all_anchors
    let S3_2 := reduce_iso (transition S3_1 v3 f3) all_anchors
    let S3_3 := reduce_iso (transition S3_2 v3 f3) all_anchors
    let S3_4 := reduce_iso (transition S3_3 v3 f3) all_anchors
    -- Gamma_4 steps (Add 4 edges to v4)
    let f4 := forbidden_for v4
    let S4_1 := reduce_iso (transition S3_4 v4 f4) all_anchors
    let S4_2 := reduce_iso (transition S4_1 v4 f4) all_anchors
    let S4_3 := reduce_iso (transition S4_2 v4 f4) all_anchors
    let S4_4 := reduce_iso (transition S4_3 v4 f4) all_anchors
    S4_4
  | _ => #[]

end FastImpl
end GraphEnumeration
