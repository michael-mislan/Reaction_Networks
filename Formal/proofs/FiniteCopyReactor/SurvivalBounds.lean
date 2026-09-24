import proofs.FiniteCopyReactor.SurvivalResolvent
import proofs.RandomViability.FirstChannelLaw

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def nonnegativeTime (t : ℝ) : ℝ≥0∞ := if 0 ≤ t then 1 else 0

theorem nonnegative_time_measurable : Measurable nonnegativeTime :=
  Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const

theorem survival_plus_event (r T : ℝ) (hr : 0 < r) (hT : 0 ≤ T) :
    survivalKernel r T+ENNReal.ofReal r*positiveConvolution (survivalKernel r) nonnegativeTime T=1 := by
  have he := (exponential_waiting_convolution r T hr.le nonnegativeTime nonnegative_time_measurable).symm
  have hi : (∫⁻ w,nonnegativeTime (T-w) ∂expMeasure r)=expMeasure r (Set.Iic T) := by
    have hh : (fun w => nonnegativeTime (T-w))=(Set.Iic T).indicator (fun _ => (1:ℝ≥0∞)) := by
      funext w
      simp only [nonnegativeTime,sub_nonneg,Set.indicator,Set.mem_Iic]
    rw [hh,lintegral_indicator measurableSet_Iic,lintegral_const,Measure.restrict_apply_univ,one_mul]
  rw [he,hi,exponential_Iic r T hr hT]
  simp only [survivalKernel,if_pos hT]
  have hE : 0 ≤ 1-Real.exp (-r*T) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    nlinarith
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le hE]
  convert ENNReal.ofReal_one using 1
  congr 1
  ring

theorem positive_convolution_mono (f g h : ℝ → ℝ≥0∞) (hgh : ∀ t,g t ≤ h t) (T : ℝ) :
    positiveConvolution f g T ≤ positiveConvolution f h T :=
  lintegral_mono (fun t => mul_le_mul_right (hgh (T-t)) (f t))

/-- One genuine-event continuation is a subprobability whenever its continuation payoff is. -/
theorem survival_candidate_le_one (r T : ℝ) (hr : 0 < r) (a : ℝ≥0∞) (ha : a ≤ 1)
    (H : ℝ → ℝ≥0∞) (hH : ∀ t,H t ≤ ENNReal.ofReal r) (hHn : ∀ t < 0,H t=0) :
    a*survivalKernel r T+positiveConvolution (survivalKernel r) H T ≤ 1 := by
  by_cases hT : 0 ≤ T
  · have hp (t : ℝ) : H t ≤ ENNReal.ofReal r*nonnegativeTime t := by
      by_cases ht : 0 ≤ t
      · simpa only [nonnegativeTime,if_pos ht,mul_one] using hH t
      · simp only [hHn t (lt_of_not_ge ht),nonnegativeTime,if_neg ht,mul_zero,le_refl]
    calc
      _ ≤ 1*survivalKernel r T+positiveConvolution (survivalKernel r)
          (fun t => ENNReal.ofReal r*nonnegativeTime t) T :=
        add_le_add (mul_le_mul_left ha _) (positive_convolution_mono _ H _ hp T)
      _ = 1 := by
        rw [one_mul,positive_convolution_const_mul _ _ (survival_kernel_measurable r)
          nonnegative_time_measurable,survival_plus_event r T hr hT]
  · rw [survival_convolution_negative r T H hHn (lt_of_not_ge hT)]
    simp only [survivalKernel,if_neg hT,mul_zero,add_zero,zero_le]

theorem causal_bounded_exponential_weight (q : ℝ) (hq : 0 ≤ q) (F : ℝ → ℝ≥0∞)
    (hF : ∀ T,F T ≤ 1) (hn : ∀ T < 0,F T=0) (T : ℝ) :
    F T ≤ ENNReal.ofReal (Real.exp (q*T)) := by
  by_cases hT : 0 ≤ T
  · exact (hF T).trans (by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hq hT)))
  · rw [hn T (lt_of_not_ge hT)]
    exact bot_le

end
end FiniteCopyReactor
