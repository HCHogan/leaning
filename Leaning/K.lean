import Mathlib
import Lean.Elab.Tactic

open Lean Elab Tactic

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
  | _ :: xs => length xs + 1

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

theorem mirror_eq_nil_iff {α : Type} : ∀ t : Tree α, mirror t = .nil ↔ t = .nil
  | .nil => by rfl
  | .node a l r => by simp [mirror]

inductive Vec (α : Type) : ℕ → Type where
  | nil : Vec α 0
  | cons : {n : ℕ} → α → Vec α n → Vec α (n + 1)

def listOfVec {α : Type} : ∀{n : ℕ}, Vec α n → List α
  | _, .nil => []
  | _, .cons a v => a :: listOfVec v

def vecOfList {α : Type} : (xs : List α) → Vec α (length xs)
  | [] => .nil
  | x :: xs => .cons x (vecOfList xs)

def length_listOfVec₁ {α : Type} : ∀(n : ℕ) (v : Vec α n), length (listOfVec v) = n
  | _, .nil => by rfl
  | n' + 1, .cons a v => by calc
      length (listOfVec (Vec.cons a v)) = length (listOfVec v) + 1 := by rfl
      _ = n' + 1 := by rw [length_listOfVec₁ n']

inductive Score : Type where
  | vs : ℕ → ℕ → Score
  | advServ : Score
  | advRecv : Score
  | gameServ : Score
  | gameRecv : Score

inductive Step : Score → Score → Prop where
  | serv_0_15 : ∀n, Step (.vs 0 n) (.vs 15 n)
  | serv_15_30 : ∀n, Step (.vs 15 n) (.vs 30 n)
  | serv_30_40 : ∀n, Step (.vs 30 n) (.vs 40 n)
  | serv_40_game: ∀n, n < 40 → Step (.vs 40 n) .gameServ

  | serv_40_adv: Step (.vs 40 40) .advServ
  | serv_adv_40: Step .advServ (.vs 40 40)
  | serv_adv_game: Step .advServ .gameServ

  | recv_0_15 : ∀n, Step (.vs n 0) (.vs n 15)
  | recv_15_30 : ∀n, Step (.vs n 15) (.vs n 30)
  | recv_30_40: ∀n, Step (.vs n 30) (.vs n 40)
  | recv_40_game: ∀n, n < 40 → Step (.vs n 40) .gameRecv

  | recv_40_adv: ∀n, Step (.vs n 40) .advRecv
  | recv_adv_40:  Step .advRecv (.vs 40 40)
  | recv_adv_game: Step .advRecv .gameRecv

theorem no_step_to_0_0 (s : Score) : ¬ Step s (.vs 0 0) := by
  intro h
  cases h

inductive Even : ℕ → Prop where
  | zero : Even 0
  | add_two : (k : ℕ) → Even k → Even (k + 2)

theorem even_4 : Even 4 := by
  have even_0 : Even 0 := .zero
  have even_2 : Even 2 := .add_two _ even_0
  have even_4 : Even 4 := .add_two _ even_2
  exact even_4

inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α) : R a b → Star R a b
  | refl (a : α) : Star R a a
  | trans (a b c : α) : Star R a b → Star R b c → Star R a c

theorem mod_two_Eq_zero_of_Even (n : ℕ) (h : Even n) : n % 2 = 0 := by
  induction h with
  | zero => rfl
  | add_two k ek ih => simp [ih]

theorem star_star_iff_star {α : Type} (R : α → α → Prop) (a b : α) :
  Star (Star R) a b ↔ Star R a b := by
  apply Iff.intro
  · intro h
    induction h with
    | base a' b' hab => exact hab
    | refl a' => exact .refl a'
    | trans a' b' c' hab hbc ihab ihbc => exact .trans a' b' c' ihab ihbc
  · intro h
    apply Star.base
    exact h

@[simp] theorem star_star_eq_star {α : Type} (R : α → α → Prop) :
  Star (Star R) = Star R := by
  apply funext
  intro a
  apply funext
  intro b
  apply propext
  apply star_star_iff_star

example : 2 * 3 < 8 := by linarith

theorem even_iff (n : ℕ) : Even n ↔ n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) := by
  constructor
  · intro heven
    cases heven with
    | zero => exact .inl rfl
    | add_two k evenk =>
      apply Or.inr
      exact ⟨k, rfl, evenk⟩
  · intro hor
    match hor with
    | .inl hzero => 
      rw [hzero]
      exact .zero
    | .inr ⟨m, hm, hevenm⟩ => 
      rw [hm]
      exact .add_two m hevenm

inductive Sorted : List ℕ → Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y) (hsorted : Sorted (y :: zs)) : Sorted (x :: y :: zs)

theorem Sorted_3_5 : Sorted [3, 5] := by
  apply Sorted.two_or_more
  · linarith
  · exact .single 5

theorem not_sorted_17_13 : ¬ Sorted [17, 13] := by
  intro h
  cases h with
  | two_or_more _ _ h _ => omega

inductive Palindrome {α : Type} : List α → Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) (xs : List α) (hxs : Palindrome xs) : Palindrome ([x] ++ xs ++ [x])

theorem Palindrome_reverse {α : Type} (xs : List α) (hxs : Palindrome xs) : Palindrome (reverse xs) := by
  induction hxs with
  | nil => exact .nil
  | single x => exact .single x
  | sandwich x xs hxs ihxs =>
    simp [reverse, reverse_append]
    exact Palindrome.sandwich x (reverse xs) ihxs

inductive IsFull {α : Type} : Tree α → Prop where
  | nil : IsFull Tree.nil
  | node (a : α) (l r : Tree α) (hl : IsFull l) (hr : IsFull r) (hiff : l = Tree.nil ↔ r = Tree.nil) : IsFull (Tree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) : IsFull (.node a .nil .nil) := by
  constructor
  · exact .nil
  · exact .nil
  · rfl

theorem IsFull_mirror {α : Type} (t : Tree α) (hfull : IsFull t) : IsFull (mirror t) := by
  induction hfull with
  | nil => exact .nil
  | node a l r hl hr hiff ihl ihr =>
    constructor
    · exact ihl
    · exact ihr
    · have h₁ := propext (mirror_eq_nil_iff l)
      rw [h₁]
      have h₂ := propext (mirror_eq_nil_iff r)
      rw [h₂]
      exact hiff

inductive Term (α β : Type) : Type where
  | var : β → Term α β
  | fn : α → List (Term α β) → Term α β

inductive WellFormed {α β : Type} (arity : α → ℕ) : Term α β → Prop where
  | var (x : β) : WellFormed arity (.var x)
  | fn (f : α) (ts : List (Term α β)) (hargs : ∀t ∈ ts, WellFormed arity t) (hlen : length ts = arity f) : WellFormed arity (.fn f ts)

inductive VariableFree {α β : Type} : Term α β → Prop where
  | fn (f : α) (ts : List (Term α β)) (hargs : ∀t ∈ ts, VariableFree t) : VariableFree (.fn f ts)

theorem not_even_two_mul_add_one (n m : ℕ) (hm : m = 2 * n + 1) : ¬ Even m := by
  intro h -- we have (n m : ℕ) (hm : m = 2 * n + 1) (h : Even m)
  induction h generalizing n with
  -- motive 接受Even m和他所有的index，这里只是m : Nat
  -- induction 把依赖Even m 的index m的东西deactivate并塞进motive
  -- motive (before generalizing): (m : ℕ) → (_ : Even m) → (m = 2 * n + 1 → False)
  -- motive (after generalizing): (m : ℕ) → (_ : Even m) → (∀n, m = 2 * n + 1 → False)
  | zero => 
    -- goal : motive 0 (Even.zero) aka 0 = 2 * n + 1 → False
    linarith
  | add_two k hk ihk => 
    -- 手里多给k : ℕ, hk : Even k, ihk : motive k (Even k)
    -- goal : motive (k + 2) (Even.add_two k hk) aka ∀n, k + 2 = 2 * n + 1 → False
    -- induction reintroduces k + 2 = 2 * n + 1 as hm and Nat n
    apply ihk (n - 1)
    omega

def nth {α : Type} : List α → Nat → Option α
  | [], _ => .none
  | x :: _, 0 => .some x
  | _ :: xs, n + 1 => nth xs n

def sum257Do (ns : List ℕ) : Option ℕ := do
  let n₂ ← nth ns 1
  let n₅ ← nth ns 4
  let n₇ ← nth ns 6
  pure (n₂ + n₅ + n₇)

def Concat1 (l₁ l₂ l₃ : List α) : Prop := l₁ ++ l₂ = l₃

inductive Concat : List α → List α → List α → Prop where
  | nil  : ∀ ys, Concat [] ys ys
  | cons : ∀ x xs ys zs, Concat xs ys zs → Concat (x :: xs) ys (x :: zs)

theorem concat_iff (l₁ l₂ l₃ : List α) : Concat l₁ l₂ l₃ ↔ l₁ ++ l₂ = l₃ := by
  constructor
  · intro h
    induction h with
    | nil ys => rfl
    | cons x xs ys zs h ih => exact ih ▸ rfl
  · rintro rfl
    induction l₁ with
    | nil => exact .nil l₂
    | cons x xs ih => exact .cons x xs l₂ (xs ++ l₂) ih

#print LawfulMonad

def sum (xs : Array Nat) : Nat := Id.run do
  let mut s := 0
  for x in xs do
    s := s + x
  return s

#print sum

/- @[reducible] -/
def id {α : Sort u} (a : α) : α := a

/- @[reducible] -/
def Id : Type → Type := @id Type

def id.pure {α : Type} : α → Id α
  | a => a

def id.bind {α : Type} (a : Id α) (f : α → Id α) : Id α := f a

def Action (σ α : Type) : Type := σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ α β : Type} (ma : Action σ α) (f : α → Action σ β) : Action σ β
  | s => 
    let (a, s') := ma s
    f a s'

instance Action.Monad {σ : Type} : Monad (Action σ) := {
  pure := Action.pure
  bind := Action.bind
}

/- instance Action.LawfulMonad {σ : Type} :  -/
/-   LawfulMonad (Action σ) := -/
/-   { -/
/-     pure_bind := by -/
/-       intro α β a f -/
/-       rfl -/
/-     bind_assoc := by -/
/-       intro α β γ f g ma -/
/-       rfl -/
/-     map_const := _ -/
/-     id_map := _ -/
/-     seqLeft_eq := _ -/
/-     seqRight_eq := _ -/
/-     pure_seq := _ -/
/-     bind_pure_comp := _ -/
/-     bind_map := _ } -/

  
example : 3 ∈ {n : ℕ | n % 2 = 1} := rfl

def increasingly : List ℕ → StateM ℕ (List ℕ)
  | [] => pure []
  | (n :: ns) => do
    let prev ← get
    if n < prev then
      increasingly ns
    else do
      set n
      let ns' ← increasingly ns
      pure (n :: ns')

#eval increasingly [1,2,3,4] |>.run' 0

/- theorem repeat_example : Even 4 ∧ Even 7 ∧ Even 3 ∧ Even 0 := by -/
/-   repeat' apply And.intro -/
/-   any_goals repeat' first -/
/-   | apply Even.add_two -/
/-   | apply Even.zero -/
/-   sorry -/

macro "intro_and_even" : tactic => `(tactic|(
  repeat' apply And.intro
  any_goals solve
  | repeat' first
    | apply Even.add_two
    | apply Even.zero
))

#eval Lean.versionString

def hypothesis : TacticM Unit := withMainContext do
  let target ← getMainTarget
  let lctx ← getLCtx
  for ldecl in lctx do
    if ! LocalDecl.isImplementationDetail ldecl then
      if ← Meta.isDefEq (LocalDecl.type ldecl) target then
        let goal ← getMainGoal
        MVarId.assign goal (LocalDecl.toExpr ldecl)
        return

def sumOdds (xs : List Nat) : Nat := Id.run do
  let mut acc := 0
  for x in xs do
    if x % 2 == 0 then continue
    if acc > 100 then break
    acc := acc + x
  return acc

def sumOdds_elaborated (xs : List Nat) : Nat := Id.run do
  let acc := 0
  let acc ← ForIn.forIn xs acc fun x acc => do
    if x % 2 == 0 then pure (.yield acc)          -- continue = 原状态 yield
    else if acc > 100 then pure (.done acc)       -- break = 原状态 done
    else pure (.yield (acc + x))                  -- 赋值 = 新状态 yield
  return acc

end K
