import Mathlib

def test_contains {n} (l : List (Fin n)) (v : Fin n) : Bool :=
  l.contains v

#eval test_contains [0, 1] 2
