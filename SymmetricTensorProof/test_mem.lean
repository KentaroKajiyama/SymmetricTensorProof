
import Mathlib.Data.List.Basic

example (a : Nat) (l : List Nat) : a ∈ a :: l := by
  exact List.mem_cons_self a l

example (a : Nat) (l : List Nat) : a ∈ a :: l := by
  exact List.mem_cons_self _ _

example (a : Nat) (l : List Nat) : a ∈ a :: l := by
  exact List.mem_cons_self
