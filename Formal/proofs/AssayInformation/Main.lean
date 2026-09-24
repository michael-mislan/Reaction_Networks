import proofs.AssayInformation.FullTimingObstruction
import proofs.AssayInformation.WindowInstance
import proofs.AssayInformation.EndpointLaw
import proofs.AssayInformation.PairedObservation

noncomputable section
namespace AssayInformation
open MeasureTheory Set DiagnosticWindows FiniteCopy

/-- Conditional finite-source result: uncertain timing, information rescue,
endpoint nonidentification, and calibrated paired-observation reconstruction.
No empirical channel quality or physical-resource interpretation is asserted. -/
theorem main :
    (∀ φ : ℝ → ℝ, Measurable φ → (∀ t, φ t ∈ Icc 0 1) →
      timingBlank φ ≤ 1/100 → 111/2000 < timingMiss φ) ∧
    (blankJoint 0 < 3/10000 ∧ 1-loadedJoint 0 < 422443/10000000) ∧
    (safeBand.Covers (blank10 (16/5)) (miss10 (16/5)) ∧ safeBand.Usable (1/100) (1/20)) ∧
    (coarseBand.Covers (blank10 (16/5)) (miss10 (16/5)) ∧ coarseBand.Unresolved (1/100) (1/20)) ∧
    (excludedBand.Covers (blank5 5) (miss5 5) ∧ excludedBand.Excluded (1/100) (1/20)) ∧
    (blankEndpointLaw 2 1 6 = blankEndpointLaw (8/3) (2/3) 4) ∧
    (∀ a R i j : ℝ, 0 < a → 0 ≤ i → i < j → j < R →
      reconstruct
        (((1-pairedExceedance (sourceRate a 1 R i) (sourceRate a 1 R j)) /
          pairedExceedance (sourceRate a 1 R i) (sourceRate a 1 R j))*((a+i)/(a+j))) i j = R) := by
  exact ⟨full_timing_obstruction,concrete_joint_rescue,
    three_decision_examples.1,three_decision_examples.2.1,three_decision_examples.2.2,
    endpoint_law_nonidentification,reconstruct_from_paired_probability⟩

end AssayInformation
