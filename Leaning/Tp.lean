theorem and_commutative (p q : Prop) : p ∧ q → q ∧ p :=
  fun hpq : p ∧ q =>
  have hp : p := And.left hpq
  have hq : q := And.right hpq
  show q ∧ p from And.intro hq hp

inductive WithNamedIndex : Type u → Type (u + 1) where
  | test1 : WithNamedIndex α
  | test2 : WithNamedIndex α → WithNamedIndex α → WithNamedIndex (α × α)


-- Note: The value of parameter 'α' must be fixed throughout the inductive declaration. 
-- Consider making this parameter an index if it must vary. [lean.inductiveParamMismatch]
/- inductive WithNamedIndex2 (α : Type u) : Type (u + 1) where -/
/-   | test1 : WithNamedIndex2 α -/
/-   | test2 : WithNamedIndex2 α → WithNamedIndex2 α → WithNamedIndex2 (α × α) -/

inductive NatParam (n : Nat) : Nat → Type u where
  | five : NatParam n 5
deriving Repr

#print NatParam

inductive MyBox (α : Type) : Type where
  | inner : α → MyBox α

#check MyBox

universe u

def F (α : Type u) : Type u := Prod α α

#check fun x => x

inductive WithTwoParameters (α : Type u) (β : Type v) : Type (max u v) where
  | test : α → β → WithTwoParameters α β
deriving Repr

inductive IndexedBox : Nat → Type u → Type (u + 1) where
  | first : α → IndexedBox 0 α
  | second : α → IndexedBox n α → IndexedBox (n + 1) (α × α)

#check IndexedBox.first 1

def myPlusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => myPlusL n k + 1

def myPlusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => myPlusR n k + 1

inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)
deriving Repr

/- def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (myPlusL n k) -/
/-   | 0, k, .nil, ys => ys -/
/-   | n + 1, k, .cons x xs, ys => (_ : Vect α (myPlusL n k + 1)) -/
