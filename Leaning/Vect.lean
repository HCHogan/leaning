inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

def Vect.replicate : (n : Nat) → α → Vect α n
  | 0, _ => .nil
  | k + 1, x => .cons x (replicate k x)

#check List.zip

def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) $ zip xs ys

#check Vect.zip (n := 5)

inductive NatOrBool where
  | nat | bool
deriving Repr

abbrev NatOrBool.asType : NatOrBool → Type
  | .nat => Nat
  | .bool => Bool

def decode (t : NatOrBool) (input : String) : Option t.asType :=
  match t with
  | .nat => input.toNat?
  | .bool =>
    match input with
    | "true" => some true
    | "false" => some false
    | _ => none

inductive NestedPairs where
  | nat : NestedPairs
  | pair : NestedPairs → NestedPairs → NestedPairs
deriving Repr

abbrev NestedPairs.asType : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2

def NestedPairs.asType_def : NestedPairs → Type
  | .nat => Nat
  | .pair t1 t2 => asType t1 × asType t2

/- example : NestedPairs.nat.asType_def = NestedPairs.nat.asType_def := Eq.refl -/

/- example : 1 = 1 := Eq.refl -/

namespace Fmt

abbrev DataList (s : List Char) : Type :=
  match s with
  | [] => Unit
  | '%' :: 'd' :: cs => Nat × DataList cs
  | '%' :: 's' :: cs => String × DataList cs
  | _ :: cs => DataList cs

abbrev Data (s : String) : Type := DataList s.toList

end Fmt

/- def printf (s : String) : Fmt.Data s → String :=  -/
