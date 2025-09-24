import Mathlib.Data.Real.Basic
import Mathlib.Topology.UniformSpace.Cauchy

example (x y z : ℝ) (hx : x ≠ 0) (h : x * y = x * z) : y = z := by
  have hyz_or := (mul_eq_mul_left_iff.mp h)
  exact hyz_or.resolve_right hx

example (P : ℝ -> Prop) (h : ∀ x : ℝ, P x) : ∀ z : ℤ, P z := by
  intro z
  simpa using h z

example (x y : ℝ) (h : x < y) : ∃ z : ℝ, x < z ∧ z < y := by
  simpa using exists_between h

#print UniformSpace

/- def foo {A : Type} (p : A → Prop) (q : A -> Prop) (∀ x : A, (p x ∧ q x)) -/
/-   : (∀ x: A, p x) ∧ (∀ x : A, q x) := -/
  
example : ∀ m n : Nat, Even n → Even (m * n) := by
  intros; simp [*, parity_simps]

def mapM [Monad m] : (α -> m β) → List α → m (List β) := traverse

#check mapM
#eval mapM (m := Id) (· + 1) [1, 2, 3, 4] -- fill implicit param manually

#print IO.Error

structure MythicalCreature where
  large : Bool
deriving Repr

structure Monster extends MythicalCreature where
  vulner : String
deriving Repr

def troll : Monster := ⟨⟨true⟩, "fuck"⟩

#eval troll.large

structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr

def nisse : Helper where
  large := false
  assistance := "household tasks"
  payment := "porridge"

structure MonstrousAssistant extends Monster, Helper where
deriving Repr

def domesticatedTroll : MonstrousAssistant where
  large := false
  assistance := "heavy labor"
  payment := "toy goats"
  vulner := "sunlight"

#check MonstrousAssistant.mk

#check traverse
