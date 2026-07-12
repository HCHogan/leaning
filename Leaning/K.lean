import Mathlib

namespace K

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

#print Decidable

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
  intro a b ha hb
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

abbrev my_money : ENat := ⊤

theorem i_have_a_lot_of_money (n : ℕ) : (n : ENat) < my_money := by
  exact WithTop.coe_lt_top n

theorem forall_one_point₁ {α : Type} (t : α) (P : α → Prop) :
  (∀ x, x = t → P x) ↔ P t := by
  apply Iff.intro
  · intro hall
    exact hall t rfl
  · intro hp x heq
    rw [heq]
    exact hp

theorem forall_one_point₂ {α : Type} (t : α) (P : α → Prop) :
  (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (fun hall => hall t rfl)
    (fun hp _ heq => heq ▸ hp)

theorem exists_one_point₁ {α : Type} (t : α) (P : α → Prop) :
  (∃ x : α, x = t ∧ P x) ↔ P t := by
  constructor
  · intro hex
    have ⟨w, hw⟩ := hex
    have ⟨hwl, hwr⟩ := hw
    rw [← hwl]
    exact hwr
  · intro hpt
    exists t

theorem exists_one_point₂ {α : Type} (t : α) (P : α → Prop) :
  (∃ x : α, x = t ∧ P x) ↔ P t :=
  ⟨
    (fun ⟨_, hxt, hpx⟩ => hxt ▸ hpx),
    (fun pt => ⟨t, rfl, pt⟩)
  ⟩

theorem two_mul_example (m n : ℕ) : 2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw [Nat.two_mul]
    _ = m + n + m :=
      by ac_rfl

def reverse {α : Type} : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def reverse_append {α : Type} : (xs ys : List α) → reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [], ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

def reverse_append_tactic {α : Type} (xs ys : List α) : reverse (xs ++ ys) = reverse ys ++ reverse xs := by
  induction xs with
  | nil => simp [reverse]
  | cons x xs hxs => simp [reverse, hxs]

def fact : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) * fact n

def map {α β : Type} (f : α → β) : List α → List β
| [] => []
| x :: xs => f x :: map f xs

theorem map_ident {α : Type} (ls : List α) : map id ls = ls := by
  induction ls with
  | nil => rfl
  | cons x xs hxs =>
    /- change x :: map id xs = x :: xs -/
    calc map id (x :: xs)
      _ = id x :: map id xs := by rfl -- definitional equal
      _ = x :: map id xs := by rfl
      _ = x :: xs := by rw [hxs]

def headOpt {α : Type} : (xs : List α) → Option α
  | [] => .none
  | x :: _ => .some x

def headPre {α : Type} : (xs : List α) → xs ≠ [] → α
  | [], hxs => (hxs rfl).elim -- absurd rfl hxs
  | x :: _, _ => x

def zip {α β : Type} : List α → List β → List (α × β)
  | x :: xs, y :: ys => ⟨x, y⟩ :: zip xs ys
  | [], _ => []
  | _, [] => []

def length {α : Type} : List α → Nat
  | [] => 0
  | _ :: xs => 1 + length xs

theorem min_add_add₁ (l m n : ℕ) : min (m + l) (n + l) = min m n + l := by
  cases Classical.em (m <= n) with
  | inl h => simp [min, h]
  | inr h => simp [min, h]

theorem min_add_add₂ (l m n : ℕ) : min (m + l) (n + l) = min m n + l := 
  if h : m ≤ n then by
    simp [min, h]
  else by
    simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
  length (zip xs ys) = min (length xs) (length ys) := by
  induction xs generalizing ys with
  | nil => simp [zip, min, length]
  | cons x xs' ih => cases ys with
    | nil => simp [zip, min, length]
    | cons y ys' => simp [zip, length, ih ys']

theorem map_zip {α α' β β' : Type} (f : α → α') (g : β → β') : ∀ xs ys,
  map (fun ⟨a, b⟩ ↦ ⟨f a, g b⟩) (zip xs ys) = zip (map f xs) (map g ys)
| [], _ => by rfl
| _ :: _, [] => by rfl
| x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]

inductive Tree (α : Type) where
  | nil : Tree α
  | node : α → Tree α → Tree α → Tree α

def mirror {α : Type} : Tree α → Tree α
  | .nil => .nil
  | .node a l r => .node a (mirror l) (mirror r)

theorem mirror_mirror₁ {α : Type} (t : Tree α) : mirror (mirror t) = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => simp [hl, hr, mirror]

theorem mirror_mirror₂ {α : Type} (t : Tree a) : mirror (mirror t) = t := by
  induction t with
  | nil => rfl
  | node a l r hl hr => calc
    mirror (mirror (.node a l r)) = .node a (mirror (mirror l)) (mirror (mirror r)) := by rfl
    _ = .node a l r := by rw [hl, hr]

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons : {n : ℕ} → α → Vec α (n + 1)

end K

