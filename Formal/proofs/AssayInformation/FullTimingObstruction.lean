import proofs.AssayInformation.TimingDual
import proofs.AssayInformation.DualMargin

namespace AssayInformation
open MeasureTheory Set

theorem full_timing_obstruction (φ : ℝ → ℝ) (hm : Measurable φ)
    (hφ : ∀ t, φ t ∈ Icc 0 1) (hblank : timingBlank φ ≤ 1/100) :
    111/2000 < timingMiss φ := by
  have hd := timing_dual φ hm hφ
  have hs := dual_source_margin
  linarith

theorem timing_information_gap :
    (∀ φ : ℝ → ℝ, Measurable φ → (∀ t, φ t ∈ Icc 0 1) →
      timingBlank φ ≤ 1/100 → 111/2000 < timingMiss φ) ∧
    (blankJoint 0 < 3/10000 ∧ 1-loadedJoint 0 < 422443/10000000) :=
  ⟨full_timing_obstruction,concrete_joint_rescue⟩

end AssayInformation
