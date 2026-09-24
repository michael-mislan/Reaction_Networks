import proofs.FiniteCopyReactor.CausalConvolution
import proofs.RandomViability.ExponentialResolvent

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def survivalKernel (q t : ℝ) : ℝ≥0∞ := if 0 ≤ t then ENNReal.ofReal (Real.exp (-q*t)) else 0

theorem survival_kernel_measurable (q : ℝ) : Measurable (survivalKernel q) := by
  exact Measurable.ite (measurableSet_le measurable_const measurable_id) (by fun_prop) measurable_const

theorem survival_convolution_negative (q T : ℝ) (F : ℝ → ℝ≥0∞)
    (hF : ∀ t < 0,F t=0) (hT : T < 0) : positiveConvolution (survivalKernel q) F T=0 := by
  unfold positiveConvolution
  have he (u : ℝ) : survivalKernel q u*F (T-u)=0 := by
    by_cases hu : 0 ≤ u
    · rw [hF (T-u) (by linarith),mul_zero]
    · simp only [survivalKernel,if_neg hu,zero_mul]
  simp only [he,lintegral_zero]

theorem survival_convolution_integral (q r T : ℝ) (hT : 0 ≤ T) :
    positiveConvolution (survivalKernel q) (survivalKernel r) T=
      ENNReal.ofReal (∫ u in (0:ℝ)..T,Real.exp (-q*u)*Real.exp (-r*(T-u))) := by
  have he (u : ℝ) : survivalKernel q u*survivalKernel r (T-u)=
      (Set.Icc 0 T).indicator (fun u => ENNReal.ofReal (Real.exp (-q*u)*Real.exp (-r*(T-u)))) u := by
    by_cases hu : 0 ≤ u
    · by_cases hv : u ≤ T
      · rw [Set.indicator_of_mem (show u ∈ Set.Icc 0 T from ⟨hu,hv⟩)]
        simp only [survivalKernel,if_pos hu,if_pos (sub_nonneg.mpr hv),ENNReal.ofReal_mul (Real.exp_pos _).le]
      · simp only [survivalKernel,if_pos hu,if_neg (show ¬0 ≤ T-u by linarith),mul_zero,
          Set.indicator_of_notMem (show u ∉ Set.Icc 0 T from fun h => hv h.2)]
    · simp only [survivalKernel,if_neg hu,zero_mul,
        Set.indicator_of_notMem (show u ∉ Set.Icc 0 T from fun h => hu h.1)]
  unfold positiveConvolution
  simp only [he]
  rw [lintegral_indicator measurableSet_Icc,← restrict_Ioc_eq_restrict_Icc]
  have hc : Continuous (fun u : ℝ => Real.exp (-q*u)*Real.exp (-r*(T-u))) := by fun_prop
  have hi : IntegrableOn (fun u : ℝ => Real.exp (-q*u)*Real.exp (-r*(T-u))) (Set.Ioc 0 T) :=
    hc.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun _ => by positivity)),
    ← intervalIntegral.integral_of_le hT]

/-- The survival kernel at a genuine event rate solves the dummy-clock resolvent. -/
theorem survival_kernel_resolvent (q r T : ℝ) (hrq : r ≤ q) :
    survivalKernel r T=survivalKernel q T+
      ENNReal.ofReal (q-r)*positiveConvolution (survivalKernel q) (survivalKernel r) T := by
  by_cases hT : 0 ≤ T
  · rw [survival_convolution_integral q r T hT]
    simp only [survivalKernel,if_pos hT]
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hrq),← ENNReal.ofReal_add (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.mpr hrq) (intervalIntegral.integral_nonneg hT (fun _ _ => by positivity)))]
    exact congrArg ENNReal.ofReal (exponential_kernel_resolvent q r T)
  · rw [survival_convolution_negative q T (survivalKernel r)
      (fun t ht => if_neg (not_le.mpr ht)) (lt_of_not_ge hT)]
    simp only [survivalKernel,if_neg hT,mul_zero,add_zero]

/-- Multiplying the survival convolution by its rate gives the exponential waiting operator. -/
theorem exponential_waiting_convolution (q T : ℝ) (hq : 0 ≤ q)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w,F (T-w) ∂expMeasure q)=ENNReal.ofReal q*positiveConvolution (survivalKernel q) F T := by
  change (∫⁻ w,F (T-w) ∂volume.withDensity (exponentialPDF q))=_
  have hD : Measurable (exponentialPDF q) := (measurable_exponentialPDFReal q).ennreal_ofReal
  have hm : Measurable (fun w : ℝ => F (T-w)) := hF.comp (measurable_const.sub measurable_id)
  rw [lintegral_withDensity_eq_lintegral_mul volume hD hm]
  have he (w : ℝ) : exponentialPDF q w=ENNReal.ofReal q*survivalKernel q w := by
    by_cases hw : 0 ≤ w
    · rw [exponentialPDF_of_nonneg hw]
      simp only [survivalKernel,if_pos hw,neg_mul,ENNReal.ofReal_mul hq]
    · simp only [exponentialPDF_of_neg (lt_of_not_ge hw),survivalKernel,if_neg hw,mul_zero]
  simp only [Pi.mul_apply,he,mul_assoc]
  exact lintegral_const_mul _ ((survival_kernel_measurable q).mul hm)

end
end FiniteCopyReactor
