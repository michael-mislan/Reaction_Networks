import proofs.PowerLawSmallRAF.SourceLowBandConcentration

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceLowBandIntensityFailureMass (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
        (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) <
      (4/5 : ℝ)
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

theorem sourceLowBandIntensityFailureMass_tendsto_zero :
    Tendsto sourceLowBandIntensityFailureMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds sourceLowBandDeficitMass_tendsto_zero
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply Finset.sum_nonneg
    intro config _
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [sourceLowBand_retained_budget, eventually_ge_atTop 4] with n hb hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha config
    by_cases hd : (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) <
        (49/50 : ℝ)*(sourceMoleculeCount n : ℝ)*sourceLowBandMean n
    · rw [if_pos hd]
      split_ifs <;> linarith only [hw]
    · have hi := mul_le_mul_of_nonneg_left (le_of_not_gt hd)
        (by positivity : 0 ≤ (19/20 : ℝ)/(sourceReactionCount n : ℝ))
      have hi' : (49/50 : ℝ)*(19/20 : ℝ)*
          ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceLowBandMean n ≤
          (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
            ∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x) := by
        convert hi using 1
        ring
      have hnot : ¬ (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
          (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (config x)) <
          (4/5 : ℝ) := not_lt_of_ge (hb.trans hi')
      simp only [if_neg hd, if_neg hnot, le_refl]

end
end PowerLawSmallRAF
