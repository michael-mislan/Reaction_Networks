import proofs.RandomViability.ExponentialLaplace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

/-- An integral identity without division by the rate difference, including equal rates. -/
theorem exponential_rate_integral (r T : ℝ) :
    r*(∫ u in (0 : ℝ)..T, Real.exp (-r*u)) = 1-Real.exp (-r*T) := by
  rw [← intervalIntegral.integral_const_mul]
  have hc : Continuous (fun u : ℝ => r*Real.exp (-(r*u))) := by fun_prop
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := T)
    (fun x _ => @hasDerivAt_neg_exp_mul_exp r x) (hc.intervalIntegrable 0 T)
  convert hh using 1
  · congr 1
    funext u
    rw [neg_mul]
  · simp only [mul_zero, neg_zero, Real.exp_zero]
    ring

/-- The physical exponential kernel solves the common-clock scalar resolvent equation. -/
theorem exponential_kernel_resolvent (q lam T : ℝ) :
    Real.exp (-lam*T) = Real.exp (-q*T) + (q-lam)*
      ∫ u in (0 : ℝ)..T, Real.exp (-q*u)*Real.exp (-lam*(T-u)) := by
  have he (u : ℝ) : Real.exp (-q*u)*Real.exp (-lam*(T-u)) =
      Real.exp (-lam*T)*Real.exp (-(q-lam)*u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul]
  have hi := exponential_rate_integral (q-lam) T
  have ht : Real.exp (-lam*T)*Real.exp (-(q-lam)*T) = Real.exp (-q*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination -Real.exp (-lam*T)*hi + ht

/-- Discounting by the common rate gives an exact one-half contraction weight. -/
theorem exponential_renewal_half_weight (q T : ℝ) (hq : 0 < q) :
    (∫⁻ u, ENNReal.ofReal (Real.exp (q*(T-u))) ∂expMeasure q) =
      ENNReal.ofReal (Real.exp (q*T))*ENNReal.ofReal (1/2 : ℝ) := by
  have he (u : ℝ) : Real.exp (q*(T-u)) = Real.exp (q*T)*Real.exp (-q*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [he, ENNReal.ofReal_mul (Real.exp_pos _).le]
  rw [lintegral_const_mul _ (by fun_prop), exponential_laplace_lintegral q q hq (by linarith)]
  have hhalf : q/(q+q) = (1/2 : ℝ) := by field_simp [ne_of_gt hq]; ring
  rw [hhalf]

end
end RandomViability
