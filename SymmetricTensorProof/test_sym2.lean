import Mathlib.Data.Sym.Sym2

def checkSym2 (n : ℕ) (e : Sym2 (Fin n)) : Prop :=
  e = Sym2.mk e.out

#check Sym2.mk
#check Sym2.out
#check Sym2.out_eq
#check Quotient.out_eq
