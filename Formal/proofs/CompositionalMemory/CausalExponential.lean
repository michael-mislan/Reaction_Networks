import proofs.CompositionalMemory.RenewalConvolution
import proofs.RandomViability.ExponentialResolvent

namespace CompositionalMemory
open Classical RandomViability MeasureTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 60000

def causalExp (r t : ℝ) : ℝ≥0∞ := if 0 ≤ t then ENNReal.ofReal (Real.exp (-r*t)) else 0

theorem causalExp_measurable (r : ℝ) : Measurable (causalExp r) := by
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem causalExp_conv_integral (q lam T : ℝ) (hT : 0 ≤ T) :
    renewalConv (causalExp q) (causalExp lam) T =
      ENNReal.ofReal (∫ u in (0 : ℝ)..T,Real.exp (-q*u)*Real.exp (-lam*(T-u))) := by
  have he (u : ℝ) : causalExp q u*causalExp lam (T-u) =
      (Set.Icc 0 T).indicator
        (fun u => ENNReal.ofReal (Real.exp (-q*u)*Real.exp (-lam*(T-u)))) u := by
    by_cases hu : 0 ≤ u <;> by_cases htu : u ≤ T <;>
      simp [causalExp,Set.indicator,Set.mem_Icc,hu,htu,sub_nonneg,
        ENNReal.ofReal_mul (Real.exp_pos _).le]
  unfold renewalConv
  simp_rw [he]
  rw [lintegral_indicator measurableSet_Icc]
  have hc : Continuous (fun u : ℝ => Real.exp (-q*u)*Real.exp (-lam*(T-u))) := by fun_prop
  rw [← ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    (Filter.Eventually.of_forall (fun u => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)),
    integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hT]

theorem causalExp_conv_negative (q lam T : ℝ) (hT : T < 0) :
    renewalConv (causalExp q) (causalExp lam) T=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  apply Filter.Eventually.of_forall
  intro u
  by_cases hu : 0 ≤ u
  · have ht : ¬0 ≤ T-u := by linarith
    simp [causalExp,ht]
  · simp [causalExp,hu]

/-- The causal exponential resolvent includes negative deadlines and equal rates. -/
theorem causalExp_resolvent (q lam : ℝ) (hql : lam ≤ q) (T : ℝ) :
    causalExp lam T = causalExp q T +
      ENNReal.ofReal (q-lam)*renewalConv (causalExp q) (causalExp lam) T := by
  by_cases hT : 0 ≤ T
  · rw [causalExp_conv_integral q lam T hT]
    simp only [causalExp,if_pos hT]
    rw [← ENNReal.ofReal_mul (sub_nonneg.mpr hql),
      ← ENNReal.ofReal_add (Real.exp_pos _).le
        (mul_nonneg (sub_nonneg.mpr hql) (intervalIntegral.integral_nonneg hT (fun u _ => by positivity)))]
    exact congrArg ENNReal.ofReal (exponential_kernel_resolvent q lam T)
  · rw [causalExp_conv_negative q lam T (lt_of_not_ge hT)]
    simp [causalExp,hT]

end
end CompositionalMemory
