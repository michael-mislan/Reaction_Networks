import proofs.PowerLawSmallRAF.VanishingLowUnion
import proofs.PowerLawSmallRAF.ShrinkingSlackEnvelope
import proofs.PowerLawSmallRAF.VariableSlackRowError

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete Filter Topology
noncomputable section

/-- Retain almost all low intensity while preserving the established
high-field row law exactly. -/
def sourceVanishingBandParameter (n : Nat) (d : SourceDegreeConfig n) (x : Molecule n) : ℝ :=
  if hlo : (d x).val < sourceShrinkingLower n
  then sourceVanishingLowOwnerParameter n d ⟨x,hlo⟩
  else sourceBandBernoulliParameter n d x

theorem sourceVanishingBandParameter_bounds (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (x : Molecule n) :
    0 ≤ sourceVanishingBandParameter n d x ∧ sourceVanishingBandParameter n d x ≤ 1 := by
  unfold sourceVanishingBandParameter
  split_ifs with hlo
  · exact sourceVanishingLowOwnerParameter_bounds n hn d ⟨x,hlo⟩
  · exact ⟨(sourceBandBernoulliParameter_bounds n hn d x).1,
      (sourceBandBernoulliParameter_bounds n hn d x).2.1⟩

theorem sourceVanishingBandParameter_low (n : Nat) (d : SourceDegreeConfig n)
    (x : SourceLowOwnerGroup n d) :
    sourceVanishingBandParameter n d x.val = sourceVanishingLowOwnerParameter n d x := by
  simp only [sourceVanishingBandParameter,dif_pos x.property]

theorem sourceVanishingBandParameter_high (n : Nat) (d : SourceDegreeConfig n)
    (x : SourceHighOwnerGroup n d) :
    sourceVanishingBandParameter n d x.val = sourceBandBernoulliParameter n d x.val := by
  simp only [sourceVanishingBandParameter,dif_neg x.property]

theorem sourceVanishingBandParameter_small (n : Nat)
    (hLU : sourceVanishingLowLower n ≤ sourceShrinkingLower n)
    (d : SourceDegreeConfig n) (x : Molecule n) (hx : (d x).val < sourceVanishingLowLower n) :
    sourceVanishingBandParameter n d x = 0 := by
  have hlo := hx.trans_le hLU
  simp [sourceVanishingBandParameter,hlo,sourceVanishingLowOwnerParameter,not_le.mpr hx]

theorem sourceVanishingBandParameter_slack (n : Nat) (hn : 4 ≤ n)
    (hε : sourceVanishingRowSlack n ≤ 1/20) (d : SourceDegreeConfig n) (x : Molecule n) :
    (Fintype.card (Reaction n) : ℝ)*sourceVanishingBandParameter n d x ≤
      (1-sourceVanishingRowSlack n)*(d x : ℝ) := by
  have hR : (0 : ℝ) < sourceReactionCount n := by
    exact_mod_cast (show 0 < sourceReactionCount n by simp [sourceReactionCount])
  by_cases hlo : (d x).val < sourceShrinkingLower n
  · rw [sourceVanishingBandParameter,dif_pos hlo]
    unfold sourceVanishingLowOwnerParameter
    split_ifs with hactive
    · simp only [card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n)]
      change (sourceReactionCount n : ℝ)*
        ((1-sourceVanishingRowSlack n)*(d x : ℝ)/(sourceReactionCount n : ℝ)) ≤ _
      exact le_of_eq (by field_simp)
    · rw [mul_zero]
      exact mul_nonneg (sourceVanishingLowRetention_bounds n).1 (Nat.cast_nonneg _)
  · rw [sourceVanishingBandParameter,dif_neg hlo]
    exact (sourceBandBernoulliParameter_bounds n hn d x).2.2.1.trans
      (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))

end
end PowerLawSmallRAF
