import proofs.FiniteCopyReactor.EndpointClockIntegral
import proofs.FiniteCopyReactor.SurvivalResolvent

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal BigOperators

variable {β : Type*} [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

theorem jump_continuation_convolution (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (F : β → ℝ → ℝ≥0∞) (hF : ∀ b,Measurable (F b)) (T : ℝ) :
    (∫⁻ y,F y.1 (T-y.2) ∂jumpClockMeasure rate hr ht)=
      positiveConvolution (survivalKernel (∑ b,rate b)) (fun u => ∑ b,ENNReal.ofReal (rate b)*F b u) T := by
  have hm : Measurable (fun y : β × ℝ => F y.1 (T-y.2)) :=
    measurable_from_prod_countable_right (fun b => (hF b).comp (measurable_const.sub measurable_id))
  rw [jump_clock_integral rate hr ht _ hm]
  simp_rw [exponential_waiting_convolution _ T ht.le _ (hF _)]
  have he (b : β) : ENNReal.ofReal (rate b/(∑ c,rate c))*ENNReal.ofReal (∑ c,rate c)=ENNReal.ofReal (rate b) := by
    rw [← ENNReal.ofReal_mul (div_nonneg (hr b) ht.le),div_mul_cancel₀ _ (ne_of_gt ht)]
  simp only [← mul_assoc,he]
  unfold positiveConvolution
  simp only [Finset.mul_sum]
  have hm' (b : β) : Measurable (fun u : ℝ => survivalKernel (∑ c,rate c) u*(ENNReal.ofReal (rate b)*F b (T-u))) :=
    (survival_kernel_measurable _).mul (measurable_const.mul ((hF b).comp (measurable_const.sub measurable_id)))
  rw [lintegral_finsetSum Finset.univ (fun b _ => hm' b)]
  apply Finset.sum_congr rfl
  intro b _
  simp only [mul_left_comm (survivalKernel _ _) (ENNReal.ofReal (rate b))]
  exact (lintegral_const_mul _ ((survival_kernel_measurable _).mul ((hF b).comp (measurable_const.sub measurable_id)))).symm

theorem jump_no_event_integral (rate : β → ℝ) (hr : ∀ b,0 ≤ rate b)
    (ht : 0 < ∑ b,rate b) (a : ℝ≥0∞) (T : ℝ) :
    (∫⁻ y : β × ℝ,(if 0 ≤ T ∧ T < y.2 then a else 0) ∂jumpClockMeasure rate hr ht)=
      a*survivalKernel (∑ b,rate b) T := by
  by_cases hT : 0 ≤ T
  · simp only [hT,true_and]
    have hm : Measurable (fun y : β × ℝ => if T < y.2 then a else 0) :=
      Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const measurable_const
    rw [jump_clock_integral rate hr ht _ hm]
    simp_rw [exponential_no_event_integral _ T ht hT a]
    rw [← Finset.sum_mul,← ENNReal.ofReal_sum_of_nonneg (fun b _ => div_nonneg (hr b) ht.le),
      ← Finset.sum_div,div_self (ne_of_gt ht),ENNReal.ofReal_one,one_mul]
    simp only [survivalKernel,if_pos hT,mul_comm]
  · simp only [hT,false_and,if_false,lintegral_zero,survivalKernel,mul_zero]

end
end FiniteCopyReactor
