import proofs.PowerLawSmallRAF.SourceOwnerWords
import proofs.PowerLawSmallRAF.SelectedTargetAverage
import proofs.PowerLawSmallRAF.SourceHighOwnerCount
import proofs.PowerLawSmallRAF.SourceShortOwnerExclusions

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

def sourceHighTargetSet (n : Nat) (d : SourceDegreeConfig n) : Finset LigationWord :=
  (Finset.univ.filter fun x : Molecule n => sourceShrinkingLower n ≤ (d x).val).image sourceOwnerWord

theorem sourceHighTargetSet_card_config (n : Nat) (B : SourceMoleculeFibreConfig n) :
    ((sourceHighTargetSet n (sourceConfigDegrees n B)).card : ℝ) =
      sourceOwnerThresholdCount n Finset.univ (sourceShrinkingLower n) B := by
  unfold sourceHighTargetSet
  rw [Finset.card_image_of_injective _ sourceOwnerWord_injective]
  change ((Finset.univ.filter fun x : Molecule n => sourceShrinkingLower n ≤ (B x).card).card : ℝ) = _
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x : Molecule n => sourceShrinkingLower n ≤ (B x).card), (1 : ℝ) := by simp
    _ = _ := by rw [Finset.sum_filter]; rfl

theorem sourceHighTargetSet_admissible_of_good (n : Nat) (B : SourceMoleculeFibreConfig n)
    (hc : sourceOwnerThresholdCount n Finset.univ (sourceShrinkingLower n) B <
      (n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n))
    (hs : ¬ ∃ x : Molecule n, x.1.val < n-2*shrinkingBandWidth n ∧ sourceShrinkingLower n ≤ (B x).card) :
    targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)) (sourceHighTargetSet n (sourceConfigDegrees n B)) := by
  refine ⟨?_,?_⟩
  · rw [sourceHighTargetSet_card_config]
    exact hc.le
  · intro w hw
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hw
    have hd : sourceShrinkingLower n ≤ (B x).card := (Finset.mem_filter.mp hx).2
    rw [sourceOwnerWord_length]
    have hl := x.1.isLt
    constructor
    · have hnot : ¬ x.1.val < n-2*shrinkingBandWidth n := fun h => hs ⟨x,h,hd⟩
      unfold molLength
      omega
    · unfold molLength
      omega

def sourceHighTargetInvalidMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    if targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)) (sourceHighTargetSet n d) then 0 else 1

theorem sourceHighTargetInvalidMass_bound (n : Nat) (hn : 4 ≤ n) :
    0 ≤ sourceHighTargetInvalidMass n ∧ sourceHighTargetInvalidMass n ≤
      sourceHighOwnerCountFailureMass n+
        sourceShortOwnerFailureMass (2-2/(n : ℝ)) n (n-2*shrinkingBandWidth n) (sourceShrinkingLower n) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  constructor
  · apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d) (by split_ifs <;> positivity)
  · unfold sourceHighTargetInvalidMass
    rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
      (fun d => if targetSetAdmissible n (n-2*shrinkingBandWidth n)
        ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)) (sourceHighTargetSet n d) then 0 else 1)]
    unfold sourceHighOwnerCountFailureMass sourceShortOwnerFailureMass
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro B _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha B
    by_cases hc : (n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n) ≤
        sourceOwnerThresholdCount n Finset.univ (sourceShrinkingLower n) B
    · simp only [if_pos hc]
      split_ifs <;> linarith only [hw]
    · by_cases hs : ∃ x : Molecule n, x.1.val < n-2*shrinkingBandWidth n ∧ sourceShrinkingLower n ≤ (B x).card
      · simp only [if_neg hc,if_pos hs]
        split_ifs <;> linarith only [hw]
      · have hv := sourceHighTargetSet_admissible_of_good n B (lt_of_not_ge hc) hs
        simp only [if_pos hv,if_neg hc,if_neg hs,mul_zero,zero_add,le_refl]

theorem sourceHighTargetInvalidMass_tendsto_zero :
    Tendsto sourceHighTargetInvalidMass atTop (𝓝 0) := by
  have ht := sourceHighOwnerCountFailureMass_tendsto_zero.add sourceHighShortOwnerFailureMass_tendsto_zero
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceHighTargetInvalidMass_bound n hn).1
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceHighTargetInvalidMass_bound n hn).2

end
end PowerLawSmallRAF
