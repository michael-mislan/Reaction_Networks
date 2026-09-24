import proofs.RandomViability.UnboundedPhysicalStep
import proofs.RandomViability.ShortIncidence

namespace RandomViability
open Classical RAF RAF.Polymer RAF.Concrete PowerLawSmallRAF FiniteCopy
noncomputable section
set_option maxHeartbeats 20000

/-- At bounded integer mass, every enabled catalytic firing exposes an
incidence among a finite collection of short catalysts and products. This is
a support statement, not an intensity or molecular-noise approximation. -/
theorem enabled_catalytic_shortIncidence {n k : ℕ} (c : SourceMoleculeFibreConfig n)
    (N : Molecule n → ℕ) (hM : countMass N ≤ k) (r : Reaction n)
    (z : Molecule n) (d : Bool) (hsel : r ∈ c z)
    (hen : ∀ y, physicalChannelInput (.inr (.inr (r,z,d))) y ≤ N y) :
    ShortIncidence k c := by
  have hi : countMass (physicalChannelInput (.inr (.inr (r,z,d)))) ≤ countMass N := by
    apply Finset.sum_le_sum
    intro y _
    exact Nat.mul_le_mul_left _ (hen y)
  have he : countMass (physicalChannelInput (.inr (.inr (r,z,d)))) =
      molLength (reactionProduct r)+molLength z := by
    cases d
    · simp only [physicalChannelInput, Bool.false_eq_true, if_false, countMass_add, countMass_single]
    · simp only [physicalChannelInput, if_true]
      rw [catalytic_count_channel_balance, countMass_add, countMass_single, countMass_single]
  rw [he] at hi
  have hz : molLength z ≤ k := by omega
  have hp : reactionProductLength r ≤ k+2 := by
    simp only [molLength_reactionProduct] at hi
    omega
  exact ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩,r,hp,hsel⟩

theorem catalytic_rate_zero_outside_occupied_source {n k : ℕ}
    (c : SourceMoleculeFibreConfig n) (hgood : ¬ShortIncidence k c)
    (V D : NNReal) (basal : Reaction n → NNReal)
    (cat : Reaction n → Molecule n → NNReal)
    (N : Molecule n → ℕ) (hM : countMass N ≤ k)
    (r : Reaction n) (z : Molecule n) (d : Bool) :
    unboundedPhysicalRate c V D basal cat N (.inr (.inr (r,z,d))) = 0 := by
  unfold unboundedPhysicalRate
  split_ifs with hen
  · have hsel : r ∉ c z := fun hs => hgood (enabled_catalytic_shortIncidence c N hM r z d hs hen)
    simp [physicalChannelRate, physicalChannelCoefficient, hsel]
  · rfl

end
end RandomViability
