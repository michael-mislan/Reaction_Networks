import proofs.FiniteCopyReactor.SurvivalResolvent
import proofs.RandomViability.WeightedRenewal

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped ENNReal

def dummyWaitingMeasure (q c T : ℝ) : Measure ℝ :=
  ENNReal.ofReal (c/q) • (expMeasure q).map (fun w => T-w)

theorem dummy_waiting_integral (q c T : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ t,F t ∂dummyWaitingMeasure q c T)=
      ENNReal.ofReal c*positiveConvolution (survivalKernel q) F T := by
  unfold dummyWaitingMeasure
  rw [lintegral_smul_measure,lintegral_map hF (by fun_prop)]
  change ENNReal.ofReal (c/q)*(∫⁻ w,F (T-w) ∂expMeasure q)=_
  rw [exponential_waiting_convolution q T hq.le F hF,← mul_assoc,
    ← ENNReal.ofReal_mul (div_nonneg hc hq.le),div_mul_cancel₀ c (ne_of_gt hq)]

theorem dummy_waiting_half_weight (q c T : ℝ) (hq : 0 < q) (hcq : c ≤ q) :
    (∫⁻ t,ENNReal.ofReal (Real.exp (q*t)) ∂dummyWaitingMeasure q c T) ≤
      ENNReal.ofReal (1/2:ℝ)*ENNReal.ofReal (Real.exp (q*T)) := by
  unfold dummyWaitingMeasure
  rw [lintegral_smul_measure,lintegral_map (by fun_prop) (by fun_prop)]
  change ENNReal.ofReal (c/q)*(∫⁻ w,ENNReal.ofReal (Real.exp (q*(T-w))) ∂expMeasure q) ≤ _
  rw [exponential_renewal_half_weight q T hq]
  calc
    _ ≤ 1*(ENNReal.ofReal (Real.exp (q*T))*ENNReal.ofReal (1/2:ℝ)) :=
      mul_le_mul_left (ENNReal.ofReal_le_one.mpr ((div_le_one hq).mpr hcq)) _
    _ = _ := by rw [one_mul,mul_comm]

/-- Dummy events have at most half the exponential weight, so their scalar renewal is unique. -/
theorem scalar_dummy_renewal_unique (q c : ℝ) (hq : 0 < q) (hc : 0 ≤ c) (hcq : c ≤ q)
    (F G B : ℝ → ℝ≥0∞) (hFm : Measurable F) (hGm : Measurable G)
    (hFw : ∀ T,F T ≤ ENNReal.ofReal (Real.exp (q*T)))
    (hGw : ∀ T,G T ≤ ENNReal.ofReal (Real.exp (q*T)))
    (hF : ∀ T,F T=B T+ENNReal.ofReal c*positiveConvolution (survivalKernel q) F T)
    (hG : ∀ T,G T=B T+ENNReal.ofReal c*positiveConvolution (survivalKernel q) G T) : F=G := by
  apply weighted_half_renewal_unique (dummyWaitingMeasure q c) F G B
    (fun T => Real.exp (q*T)) hFm hGm (by fun_prop) hFw hGw
  · intro T
    rw [dummy_waiting_integral q c T hq hc F hFm]
    exact hF T
  · intro T
    rw [dummy_waiting_integral q c T hq hc G hGm]
    exact hG T
  · intro T
    exact dummy_waiting_half_weight q c T hq hcq

end
end FiniteCopyReactor
