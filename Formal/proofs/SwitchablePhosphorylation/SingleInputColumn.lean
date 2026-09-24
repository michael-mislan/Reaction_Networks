import Mathlib

namespace SwitchablePhosphorylation

/-- One association event consumes S1,F and produces D1; its pool changes cancel. -/
theorem alpha1_pool_cancellation (flux : ℝ) : -flux + flux = 0 := by ring

theorem alpha1_relative_input (a u s f : ℝ) :
    a * (1 + u) * s * f - a * s * f = u * (a * s * f) := by ring

theorem alpha1_at_equilibrium (r q s f : ℝ) (hs : s ≠ 0) (hf : f ≠ 0) :
    ((1 + r) * q / (s * f)) * s * f = (1 + r) * q := by field_simp

theorem alpha1_positive (a u eta : ℝ) (ha : 0 < a)
    (hu : |u| < eta) (he : eta < 1) : 0 < a * (1 + u) := by
  have h := neg_abs_le u
  apply mul_pos ha
  linarith

end SwitchablePhosphorylation
