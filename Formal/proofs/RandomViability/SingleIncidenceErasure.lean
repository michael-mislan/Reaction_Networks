import proofs.RandomViability.LocalIncidenceClassification
import proofs.RandomViability.SingleIncidenceRewardNoise

set_option Elab.async false
namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 40000

/-- Removing the local catalyst leaves this specific reward drift unchanged,
because the removed channel preserves the modified mass in both directions.
This is a pointwise identity, not monotonicity of reactor trajectories. -/
theorem half_modified_drift_erase {n : ℕ} (c : SourceMoleculeFibreConfig n)
    (z₀ : Molecule n) (r₀ : Reaction n) (V : NNReal)
    (basal : Reaction n → NNReal) (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) :
    markedRewardDrift c V basal cat
      (halfModifiedInputReward (reactionProduct r₀) (ligationNonfoodMassGain r₀) V) N =
    markedRewardDrift (eraseLocalIncidence c z₀ r₀) V basal cat
      (halfModifiedInputReward (reactionProduct r₀) (ligationNonfoodMassGain r₀) V) N := by
  unfold markedRewardDrift
  apply Finset.sum_congr rfl
  intro ch _
  rcases ch with external | (⟨r,d⟩ | ⟨r,z,d⟩)
  · simp only [halfModifiedInputReward,mul_zero]
  · rfl
  · by_cases hz : z = z₀
    · subst z
      by_cases hr : r = r₀
      · subst r
        simp only [half_modified_local_reward_zero,mul_zero]
      · have hmem : (r ∈ eraseLocalIncidence c z₀ r₀ z₀) ↔ r ∈ c z₀ := by
          simp [eraseLocalIncidence,hr]
        simp only [unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,hmem]
    · have hrow : eraseLocalIncidence c z₀ r₀ z = c z := if_neg hz
      simp only [unboundedPhysicalRate,physicalChannelRate,physicalChannelCoefficient,hrow]

end
end RandomViability
