import proofs.AssayInformation.FullTimingObstruction

namespace AssayInformation
open MeasureTheory Set

theorem decision_gap (φ : ℝ → ℝ) (hm : Measurable φ)
    (hφ : ∀ t, φ t ∈ Icc 0 1) (hb : timingBlank φ ≤ 1/100) :
    132557/10000000 < timingMiss φ - (1-loadedJoint 0) := by
  have ht := full_timing_obstruction φ hm hφ hb
  have hj := concrete_joint_rescue.2
  linarith

/-- Scalar consequence of the classwise total-variation expectation bounds.
The measure-theoretic TV bridge is proved conventionally in the paper. -/
theorem discrepancy_budget (fp miss fp' miss' d0 d1 : ℝ)
    (hd : 211/2000 - 5*fp < miss)
    (hf : fp ≤ fp'+d0) (hm : miss ≤ miss'+d1) (hfp : fp' ≤ 1/100) :
    111/2000 - 5*d0-d1 < miss' := by
  linarith

theorem robust_channel_arithmetic (F M e fp miss : ℝ)
    (hF0 : 0 ≤ F) (hF : F < 32/1000) (hM : M < 35/1000)
    (he : e < 19/1000)
    (hf : fp ≤ F/100) (hm : miss ≤ 1-(99/100)*(1-M-e*F)) :
    fp < 32/100000 ∧ miss < 565649/12500000 := by
  have hp : e*F < (19/1000:ℝ)*(32/1000) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr he.le) hF0]
  constructor <;> linarith

end AssayInformation
