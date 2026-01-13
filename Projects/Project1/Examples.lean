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



namespace NatMul

def n : ℕ := 20

def xs : Vector Nat n :=
⟨
  #[7, 42, 3, 19, 11, 14, 56, 2, 91, 27,
   1, 10, 1, 5, 73, 21, 49, 16, 8, 1],
  by decide
⟩

def mH  := compute_m_H n
#check mH
#eval mH.time
def m := mH.ret.1
def H := mH.1.2
#eval m
#eval H

def albero := build ℕ n xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval query ℕ n albero.ret 0 3

def albero1 := update ℕ n albero.ret 5 3
#check albero1
#eval albero1.time
#eval albero1.ret.a


end NatMul



namespace NatSum

local instance NatWithSum : Monoid Nat where
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

def albero := @build ℕ NatWithSum n xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval @query ℕ NatWithSum n albero.ret 2 8

def albero1 := @update ℕ NatWithSum n albero.ret 5 3
#check albero1
#eval albero1.time
#eval albero1.ret.a

end NatSum


namespace NatMax
#check Nat.max_zero
#check Nat.zero_max
#check Nat.max_assoc

local instance maxMonoid : Monoid Nat where
  mul := max
  one := 0
  one_mul := Nat.zero_max
  mul_one := Nat.max_zero
  mul_assoc := Nat.max_assoc

def n : ℕ := 20

def xs : Vector Nat n :=
⟨
  #[7, 42, 3, 19, 88, 14, 56, 2, 91, 27,
   64, 10, 35, 5, 73, 21, 49, 16, 8, 60],
  by decide
⟩


def mH  := compute_m_H n
#check mH
#eval mH.time
def m := mH.ret.1
def H := mH.1.2
#eval m
#eval H

def albero := build ℕ n xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval @query ℕ maxMonoid n albero.ret 0 3
#eval @query ℕ maxMonoid n albero.ret 5 30
#eval @query ℕ maxMonoid n albero.ret 11 19

def albero1 := @update ℕ maxMonoid n albero.ret 5 3
#check albero1
#eval albero1.time
#eval albero1.ret.a

end NatMax


namespace NatGcd

local instance : Monoid ℕ where
  mul := Nat.gcd
  one := 0
  mul_one := Nat.gcd_zero_right
  one_mul := Nat.gcd_zero_left
  mul_assoc := Nat.gcd_assoc

def n : ℕ := 20

def xs : Vector Nat n :=
⟨
  #[7*2, 42, 3*2, 19*2*3, 88*3, 14*3, 56*3, 2*3*7, 91, 27*7,
   64*7, 10*7, 35, 5, 73*5, 21*5, 49*5, 16*5, 8, 60],
  by decide
⟩


def mH  := compute_m_H n
#check mH
#eval mH.time
def m := mH.ret.1
def H := mH.1.2
#eval m
#eval H

def albero := build ℕ n xs

#check albero
#eval albero.time
#eval albero.ret.a
#eval query ℕ n albero.ret 0 3
#eval query ℕ n albero.ret 25 30
#eval query ℕ n albero.ret 12 18

def albero1 := update ℕ n albero.ret 5 3
#check albero1
#eval albero1.time
#eval albero1.ret.a

end NatGcd


end Examples
