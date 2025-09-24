structure RawInput where
  name : String
  birthYear : String

structure MySubtype {α : Type} (p : α → Prop) where
  val : α
  property : p val

def FastPos : Type := {x : Nat // x > 0}

def one : FastPos := ⟨1, by simp⟩

instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp⟩

def myAsFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else
    none

#print Vector

#check Vector.{0}

#check Prop

#check Nat

inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
deriving Repr

