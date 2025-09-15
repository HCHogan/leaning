import Mathlib.Algebra.Group.Defs

def hello := "world"

def foo (_ : Vector α n) : Nat := n

abbrev N : Type := Nat

structure PPoint (α : Type) where
  ppoint ::
  x : α
  y : α
  deriving Repr

def natOrigin : PPoint Nat := { x := .zero, y := .zero }

inductive Sign where
  | pos
  | neg
  deriving Repr

def posOrNeg (s : Sign) : match s with | .pos => Nat | .neg => Int :=
  match s with
  | .pos => (3 : Nat)
  | .neg => (-3 : Int)

#check (posOrNeg Sign.pos)

def lists : List Nat := [2, 3, 5, 7]

inductive List' (α : Type) where
  | nil : List' α
  | cons : α → List' α → List' α

def explicitPrimesUnder10 : List Nat :=
  .cons 2 (.cons 3 (.cons 5 .nil))

def fives : String × Int := { fst := "five", snd := 5 }

def zero1 (p : (Nat × Nat)) : (Nat × Nat) :=
  { p with fst := 0 }

def even : Nat → Bool
  | .zero => true
  | .succ k => not (even k)

def onePlusOneIsTwo : 1 + 1 = 2 := rfl

#check onePlusOneIsTwo

theorem onePlusOneIsTwo' : 1 + 1 = 2 := by 
  simp

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | .intro a _ => .inl a

class MyAdd (α : Type) where
  add : α → α → α

#print MyAdd

#print Group

#check 1 > 2

