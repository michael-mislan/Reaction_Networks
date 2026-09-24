import proofs.RandomViability.JumpClockKernel
import Mathlib.MeasureTheory.Measure.WithDensity

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000

theorem exponential_density_laplace (r s x : ℝ) (hr : 0 < r) (hrs : 0 < r+s) :
    exponentialPDF r x * ENNReal.ofReal (Real.exp (-s*x)) =
      ENNReal.ofReal (r/(r+s)) * exponentialPDF (r+s) x := by
  by_cases hx : 0 ≤ x
  · rw [exponentialPDF_of_nonneg hx, exponentialPDF_of_nonneg hx,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have he : Real.exp (-((r+s)*x)) = Real.exp (-(r*x))*Real.exp (-s*x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    field_simp
  · rw [exponentialPDF_of_neg (lt_of_not_ge hx), exponentialPDF_of_neg (lt_of_not_ge hx)]
    simp

theorem exponential_laplace_lintegral (r s : ℝ) (hr : 0 < r) (hrs : 0 < r+s) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂expMeasure r = ENNReal.ofReal (r/(r+s)) := by
  change ∫⁻ x, ENNReal.ofReal (Real.exp (-s*x)) ∂volume.withDensity (exponentialPDF r) = _
  have hm : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hm' : Measurable (exponentialPDF (r+s)) := (measurable_exponentialPDFReal (r+s)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul volume hm (by fun_prop)]
  simp only [Pi.mul_apply, exponential_density_laplace r s _ hr hrs]
  rw [lintegral_const_mul _ hm',
    lintegral_exponentialPDF_eq_one hrs, mul_one]

end
end RandomViability
