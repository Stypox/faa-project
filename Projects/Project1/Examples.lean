import Mathlib.Tactic
import Projects.Project1.timeAPI
import Projects.Project1.SegmentTree
import Projects.Project1.Build
import Projects.Project1.Query
import Projects.Project1.Update

set_option autoImplicit false

section Examples


#check (inferInstance : AddMonoid Nat)
#check Monoid
#check Additive Nat
#check (inferInstance : Monoid Nat)
--#check (inferInstance : Monoid (Additive Nat))

section NatSum

instance NatWithSum : Monoid Nat where
  mul := Nat.add
  one := 0
  mul_one := Nat.add_zero
  one_mul := Nat.zero_add
  mul_assoc := Nat.add_assoc

def n : ℕ := 9

variable (xs : Vector ℕ n :=
  ⟨#[5, 8, 6, 3, 2, 7, 2, 6, 0],
    by decide⟩)


def mH  := compute_m_H n
#check mH
#eval mH.time
def m := mH.ret.1
def H := mH.1.2
#eval m
#eval H

def albero := build ℕ NatWithSum n xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval query ℕ NatWithSum 9 albero.ret 2 8

def albero1 := update ℕ NatWithSum 9 albero.ret 5 3
#check albero1
#eval albero1.ret.a



end NatSum


end Examples
