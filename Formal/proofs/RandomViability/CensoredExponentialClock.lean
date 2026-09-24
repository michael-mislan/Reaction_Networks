import proofs.RandomViability.ExponentialLaplace
import proofs.RandomViability.FirstChannelLaw

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory Set
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

theorem exponential_truncated_laplace (r s T : ℝ) (hr : 0 < r)
    (hu : 0 < r+s) (hT : 0 ≤ T) :
    (∫⁻ t in Iic T,ENNReal.ofReal (Real.exp (-s*t)) ∂expMeasure r) =
      ENNReal.ofReal (r/(r+s))*ENNReal.ofReal (1-Real.exp (-(r+s)*T)) := by
  change (∫⁻ t,ENNReal.ofReal (Real.exp (-s*t))
    ∂(volume.withDensity (exponentialPDF r)).restrict (Iic T)) = _
  rw [restrict_withDensity measurableSet_Iic]
  have hm : Measurable (exponentialPDF r) := (measurable_exponentialPDFReal r).ennreal_ofReal
  have hm' : Measurable (exponentialPDF (r+s)) := (measurable_exponentialPDFReal (r+s)).ennreal_ofReal
  rw [lintegral_withDensity_eq_lintegral_mul _ hm (by fun_prop)]
  simp only [Pi.mul_apply,exponential_density_laplace r s _ hr hu]
  rw [lintegral_const_mul _ hm',lintegral_exponentialPDF_eq_antiDeriv hu]
  simp only [if_pos hT,neg_mul]

theorem exponential_Ioi (r T : ℝ) (hr : 0 < r) (hT : 0 ≤ T) :
    expMeasure r (Ioi T) = ENNReal.ofReal (Real.exp (-r*T)) := by
  letI := isProbabilityMeasure_expMeasure hr
  rw [← compl_Iic,measure_compl measurableSet_Iic (measure_ne_top _ _),
    measure_univ,exponential_Iic r T hr hT]
  have he : 0 ≤ 1-Real.exp (-r*T) := by
    have hh := Real.exp_le_one_iff.mpr (show -r*T ≤ 0 by nlinarith)
    linarith
  rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub 1 he]
  congr 1
  ring

/-- A clock stopped at T has a no-jump payoff as well as a jump payoff. -/
theorem exponential_censored_weight_integral (r s T w : ℝ) (hr : 0 < r)
    (hu : 0 < r+s) (hT : 0 ≤ T) (hw : 0 ≤ w) :
    (∫⁻ t,(if t ≤ T then ENNReal.ofReal w*ENNReal.ofReal (Real.exp (-s*t))
      else ENNReal.ofReal (Real.exp (-s*T))) ∂expMeasure r) =
      ENNReal.ofReal (w*r/(r+s)*(1-Real.exp (-(r+s)*T))+Real.exp (-(r+s)*T)) := by
  change (∫⁻ t,(Iic T).piecewise (fun t => ENNReal.ofReal w*ENNReal.ofReal (Real.exp (-s*t)))
    (fun _ => ENNReal.ofReal (Real.exp (-s*T))) t ∂expMeasure r) = _
  rw [lintegral_piecewise measurableSet_Iic,lintegral_const_mul _ (by fun_prop),
    exponential_truncated_laplace r s T hr hu hT,lintegral_const,
    Measure.restrict_apply_univ,compl_Iic,exponential_Ioi r T hr hT]
  have he : 0 ≤ 1-Real.exp (-(r+s)*T) := by
    have hh := Real.exp_le_one_iff.mpr (show -(r+s)*T ≤ 0 by nlinarith)
    linarith
  rw [← ENNReal.ofReal_mul (div_nonneg hr.le hu.le),← ENNReal.ofReal_mul hw,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le,← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1
  have hex : Real.exp (-s*T)*Real.exp (-r*T) = Real.exp (-(r+s)*T) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hex]
  ring

end
end RandomViability
