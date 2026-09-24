import Mathlib

namespace SwitchablePhosphorylation

/-- Quadratic Lyapunov derivative bound on a chosen capture ball. -/
theorem capture_derivative (r R lam K deriv : ℝ)
    (hR : r ≤ R) (hK : 0 ≤ K)
    (hd : deriv ≤ -2 * lam * r^2 + 2 * K * r^3) :
    deriv ≤ -2 * (lam - K * R) * r^2 := by
  have h := mul_nonneg (mul_nonneg hK (sub_nonneg.mpr hR)) (sq_nonneg r)
  nlinarith

theorem capture_decay_positive (lam K R : ℝ) (h : K * R < lam) :
    0 < lam - K * R := by linarith

end SwitchablePhosphorylation
