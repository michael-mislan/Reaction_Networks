import proofs.FiniteCopyReactor.EndpointMeasurability
import proofs.FiniteCopyReactor.SurvivalResolvent

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal BigOperators

def causalClockEndpoint {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (q : ℝ) (f : α → ℝ≥0∞) (x : α) (T : ℝ) : ℝ≥0∞ :=
  if 0 ≤ T then clockEndpoint P q T f x else 0

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] [Fintype β]

theorem causal_clock_measurable (P : MarkedKernel α β) (q : ℝ) (f : α → ℝ≥0∞) :
    Measurable (fun p : ℝ × α => causalClockEndpoint P q f p.2 p.1) :=
  Measurable.ite (measurableSet_le measurable_const measurable_fst)
    (clock_endpoint_measurable P q f) measurable_const

omit [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α] in
theorem causal_clock_le_one (P : MarkedKernel α β) (q : ℝ) (hq : 0 ≤ q)
    (f : α → ℝ≥0∞) (hf : ∀ x,f x ≤ 1) (x : α) (T : ℝ) : causalClockEndpoint P q f x T ≤ 1 := by
  by_cases hT : 0 ≤ T
  · exact (if_pos hT).trans_le (clock_endpoint_le_one P q T hq hT f hf x)
  · simp only [causalClockEndpoint,if_neg hT,zero_le]

theorem causal_clock_survival_renewal (P : MarkedKernel α β) (q : ℝ) (hq : 0 ≤ q)
    (f : α → ℝ≥0∞) (x : α) (T : ℝ) :
    causalClockEndpoint P q f x T=f x*survivalKernel q T+
      ENNReal.ofReal q*positiveConvolution (survivalKernel q)
        (fun u => ∑ b,ENNReal.ofReal (P.prob x b)*causalClockEndpoint P q f (P.next x b) u) T := by
  let H := fun u => ∑ b,ENNReal.ofReal (P.prob x b)*causalClockEndpoint P q f (P.next x b) u
  have hmH : Measurable H := by
    apply Finset.measurable_sum
    intro b _
    have hh := (causal_clock_measurable P q f).comp
      (show Measurable (fun u : ℝ => (u,P.next x b)) from measurable_id.prodMk measurable_const)
    exact measurable_const.mul hh
  have hnH (u : ℝ) (hu : u < 0) : H u=0 := by
    simp only [H,causalClockEndpoint,if_neg (not_le.mpr hu),mul_zero,Finset.sum_const_zero]
  by_cases hT : 0 ≤ T
  · have he := (exponential_waiting_convolution q T hq H hmH).symm.trans
      (exponential_residual_integral q T H hmH hnH)
    rw [show causalClockEndpoint P q f x T=clockEndpoint P q T f x from if_pos hT]
    change clockEndpoint P q T f x=f x*survivalKernel q T+
      ENNReal.ofReal q*positiveConvolution (survivalKernel q) H T
    rw [he]
    have hi : (∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*
        ∑ b,ENNReal.ofReal (P.prob x b)*clockEndpoint P q u f (P.next x b))=
        ∫⁻ u in Set.Ioc 0 T,ENNReal.ofReal (q*Real.exp (-q*(T-u)))*H u := by
      apply setLIntegral_congr_fun measurableSet_Ioc
      intro u hu
      simp only [H,causalClockEndpoint,if_pos hu.1.le]
    have hh := clock_endpoint_renewal P q T hq hT f x
    rw [hi] at hh
    simpa only [survivalKernel,if_pos hT,mul_comm (f x)] using hh
  · rw [survival_convolution_negative q T H hnH (lt_of_not_ge hT)]
    simp only [causalClockEndpoint,survivalKernel,if_neg hT,mul_zero,zero_add]

end
end FiniteCopyReactor
