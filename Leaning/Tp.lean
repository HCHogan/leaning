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

-- Comparing types using definitional equality means that everything involved in definitional equality, 
-- including the internals of function definitions, becomes part of the interface of programs that use dependent types and indexed families.
def appendL : Vect α n → Vect α k → Vect α (myPlusL n k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x $ appendL xs ys

def plusR_zero_left : (k : Nat) → k = myPlusR 0 k
  | 0 => by rfl
  | n + 1 => congrArg (· + 1) (plusR_zero_left n)

def plusR_succ_left (n : Nat) : (k : Nat) → myPlusR (n + 1) k = myPlusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
-- h : myPlusR (n + 1) k = myPlusR n k + 1
-- myPlusR (n + 1) (k + 1) definitional equals to myPlusR (n + 1) k + 1
-- myPlusR (n + 1) k + 1 = myPlusR n k + 1 + 1
-- => myPlusR (n + 1) (k + 1) = myPlusR n (k + 1) + 1 ∎

def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (myPlusR n k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => plusR_succ_left n k ▸ .cons x (appendR n k xs ys)

theorem plusR_zero_left_t1 (k : Nat) : k = myPlusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold myPlusR
    rw [←ih]

theorem plusR_zero_left_t2 (k : Nat) : k = myPlusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [myPlusR]
    assumption

theorem plusR_zero_left_t3 (k : Nat) : k = myPlusR 0 k := by
  induction k <;> simp [myPlusR] <;> assumption

#check And
#check False

axiom unsound : False

variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left -- have h : p := s; t => (fun (h : p) => t) s
  have hq : q := h.right
  show q ∧ p from ⟨hq, hp⟩

example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp
  show q from h.right

open Classical

variable (p : Prop)

#check em p

example (h : ¬¬p) : p :=
  Or.elim (em p)
    (fun h1 : p => h1)
    (fun hnp : ¬p => absurd hnp h)

example (h : ¬¬p) : p :=
  byCases
    (fun h1 : p => h1)
    (fun h1 : ¬p => absurd h1 h)

example (h : ¬¬p) : p :=
  byContradiction (fun h1 : ¬p => show False from h h1)

-- ¬p equals to p -> False
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p => show False from hnq (hpq hp)

-- we can consider the implication of props as ∀ x : p, q, where q does not depend on x

/- example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y := _ -/

#check @Eq.refl.{u}
#check @Eq.symm.{u}
#check @Eq.trans.{u}


example (f : α → β) (a : α) : (fun x => f x) a = f a := Eq.refl _
example (f : α → β) (a : α) : (fun x => f x) a = f a := rfl

example : 1 + 1 = 2 := by rfl

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop) (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

example : a = e :=
  calc
    a = b      := by rw [h1]
    _ = c + 1  := by rw [h2]
    _ = d + 1  := by rw [h3]
    _ = 1 + d  := by rw [Nat.add_comm]
    _ = e      := by rw [h4]

#reduce (1 : Nat) + 1
opaque two : Nat := 1 + 1
/- example : two = 1 + 1 := by rfl -/
