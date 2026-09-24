import proofs.RandomViability.ExponentialResolvent

namespace StartupCount
open MeasureTheory RandomViability
noncomputable section
set_option maxHeartbeats 40000

def affineEnvelope (c b f t : ℝ) : ℝ :=
  Real.exp (-c*t)*f + (1-Real.exp (-c*t))*b

theorem affineEnvelope_nonneg (c b f t : ℝ) (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hf : 0 ≤ f) (ht : 0 ≤ t) : 0 ≤ affineEnvelope c b f t := by
  have he : Real.exp (-c*t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  exact add_nonneg (mul_nonneg (Real.exp_pos _).le hf) (mul_nonneg (by linarith) hb)

/-- Exact first-jump renewal of the affine envelope, including no-jump mass. -/
theorem affine_renewal_identity (R c b f T : ℝ) :
    Real.exp (-R*T)*f +
      ((R-c)*f+c*b)*(∫ u in (0 : ℝ)..T,Real.exp (-R*u)*Real.exp (-c*(T-u))) +
      R*b*((∫ u in (0 : ℝ)..T,Real.exp (-R*u))-
        (∫ u in (0 : ℝ)..T,Real.exp (-R*u)*Real.exp (-c*(T-u)))) =
      affineEnvelope c b f T := by
  have h0 := exponential_rate_integral R T
  have hc := exponential_kernel_resolvent R c T
  unfold affineEnvelope
  linear_combination b*h0 - (f-b)*hc

/-- A generator bound S-R*f <= -c*f+c*b gives a first-jump
supersolution. This keeps the inhomogeneous equilibrium term. -/
theorem affine_renewal_supersolution (R c b f S T : ℝ) (hT : 0 ≤ T)
    (hS : S ≤ (R-c)*f+c*b) :
    Real.exp (-R*T)*f +
      S*(∫ u in (0 : ℝ)..T,Real.exp (-R*u)*Real.exp (-c*(T-u))) +
      R*b*((∫ u in (0 : ℝ)..T,Real.exp (-R*u))-
        (∫ u in (0 : ℝ)..T,Real.exp (-R*u)*Real.exp (-c*(T-u)))) ≤
      affineEnvelope c b f T := by
  have hi : 0 ≤ ∫ u in (0 : ℝ)..T,Real.exp (-R*u)*Real.exp (-c*(T-u)) :=
    intervalIntegral.integral_nonneg hT (fun _ _ => by positivity)
  have hh := mul_le_mul_of_nonneg_right hS hi
  rw [← affine_renewal_identity R c b f T]
  linarith only [hh]

end
end StartupCount
