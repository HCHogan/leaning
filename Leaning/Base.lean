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
  
