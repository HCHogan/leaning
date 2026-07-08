import Mathlib

variable {α : Type} (s t : Set α)

#check s ⊆ t

#eval (default : Nat)
example (n : Nat) : 0 + n = n := Nat.zero_add n

example (α : Type) (a b : α) (p : α → Prop)
    (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

def safeDiv (a b : Nat) : Nat :=
  if h : b != 0 then a / b -- dependent if, get h from decidable
  else 0

#check Eq.rec
#check Nat.rec

example {A : Type} {B : Type} {P : A → B → Prop} 
  (h : (a : A) → Σ' b : B, P a b) : Σ' f : A → B, (a : A) → P a (f a) :=
  ⟨ fun a => (h a).1, fun a => (h a).2 ⟩

#eval decide (3 < 5)

example [inst : Decidable (3 < 5)] : String :=
  match inst with
  | .isTrue _ => "yes"
  | .isFalse _ => "no"

def find? (p : Prop) [Decidable p] : Option (PLift p) :=
  if h : p then some ⟨h⟩ else none

example (p q : Prop) : p ∧ q → q ∧ p :=
  fun ⟨hp, hq⟩ => ⟨hq, hp⟩

example (h : 0 + x = 0 + y + 2) : x = y + 2 := by
  repeat rw [zero_add] at h
  exact h

theorem my_map {α β : Type} (f : α → β) : Nonempty α → Nonempty β
  | ⟨ val ⟩ => ⟨ f val ⟩

def nonempty_a {α : Type} [inst : Inhabited α] : Nonempty α :=
  ⟨ inst.default ⟩

#reduce Classical.choice (nonempty_a (α := Nat))

def minus3 : Nat → List Nat
| 0 => []
| n + 1 => (n + 1) :: minus3 (n - 2)
decreasing_by exact Nat.sub_lt_succ n 2

#print minus3

#reduce minus3 12

/- example : minus3 12 = [12, 9, 6, 3] := rfl -/

def make_finite_list : Nat → List Nat
| 0 => []
| n + 1 => (n + 1) :: make_finite_list ((n + 1) / 2)

#reduce make_finite_list 10

def forall_a_in_a_a (α : Type) : α → α :=
  sorry

def T : Type 1 := (α : Type) → α → α

inductive Bar : Type 1 → Type _ where
  | mk : (α : Type 1) → Bar α

#print Bar

inductive Bar2 : Type 1 → Type 2 where
  | mk : (α : Type 1) → Bar2 α
  | unit : Bar2 (ULift Nat)

#print Bar2

inductive Baz : Type _ where
  | mk : (α : Type) → Baz

#print Baz

inductive IndexType : Type u → Type (u+1) 
| mk (A : Type u) (a : A) : IndexType A

inductive MyEven : Nat → Prop where
  | zero : MyEven 0

#print MyEven.rec

#check List.cons

theorem fst_of_two_props : ∀ α β : Prop, α → β → α := by
  intro a b
  intro ha hb
  exact ha

theorem and_swap : ∀ a b : Prop, a ∧ b → b ∧ a := by
  intro a b hab
  apply And.intro
  · exact And.right hab
  · exact And.left hab

theorem Eq_trans_symm {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) : a = c := by
  apply Eq.trans
  · exact hab
  · apply Eq.symm
    exact hcb

theorem my_add_zero (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ n' ih => simp only [ih, ← add_assoc]


