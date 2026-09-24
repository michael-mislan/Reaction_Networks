import proofs.PowerLawSmallRAF.SourceBandUnionIntensity
import proofs.PowerLawSmallRAF.SourceHighBandCoverage
import proofs.PowerLawSmallRAF.SourceLowBandIntensity

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceHighUnionFailureMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    (if sourceHighUnionParameter n d < (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) then 1 else 0)

def sourceLowUnionFailureMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    (if sourceLowUnionParameter n d < 1-Real.exp (-(4/5 : ℝ)) then 1 else 0)

private theorem sourceExponent_gt_one (n : Nat) (hn : 4 ≤ n) : 1 < 2-2/(n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h : (2 : ℝ)/(n : ℝ) < 1 :=
    (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
  linarith

theorem sourceHighUnionFailureMass_le (n : Nat) (hn : 4 ≤ n)
    (hAL : sourceLowBandLower n ≤ sourceShrinkingLower n) :
    0 ≤ sourceHighUnionFailureMass n ∧
      sourceHighUnionFailureMass n ≤ sourceHighBandCoverageFailureMass n := by
  have ha := sourceExponent_gt_one n hn
  constructor
  · apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d) (by split_ifs <;> norm_num)
  · unfold sourceHighUnionFailureMass
    rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
      (fun d => if sourceHighUnionParameter n d < (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) then 1 else 0)]
    unfold sourceHighBandCoverageFailureMass
    apply Finset.sum_le_sum
    intro B _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha B
    have hq := sourceHighUnionParameter_ge_band_intensity n hn (sourceConfigDegrees n B) hAL
    rw [sourceDegreeBandSum_config] at hq
    by_cases hbad : sourceHighUnionParameter n (sourceConfigDegrees n B) <
        (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ))
    · have hb := lt_of_le_of_lt hq hbad
      simp only [if_pos hbad, if_pos hb, mul_one, le_refl]
    · simp only [if_neg hbad, mul_zero]
      split_ifs <;> linarith only [hw]

theorem sourceLowUnionFailureMass_le (n : Nat) (hn : 4 ≤ n)
    (hLU : sourceShrinkingLower n ≤ sourceShrinkingUpper n) :
    0 ≤ sourceLowUnionFailureMass n ∧
      sourceLowUnionFailureMass n ≤ sourceLowBandIntensityFailureMass n := by
  have ha := sourceExponent_gt_one n hn
  constructor
  · apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d) (by split_ifs <;> norm_num)
  · unfold sourceLowUnionFailureMass
    rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
      (fun d => if sourceLowUnionParameter n d < 1-Real.exp (-(4/5 : ℝ)) then 1 else 0)]
    unfold sourceLowBandIntensityFailureMass
    apply Finset.sum_le_sum
    intro B _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha B
    have hq := sourceLowUnionParameter_ge_band_intensity n hn (sourceConfigDegrees n B) hLU
    rw [sourceDegreeBandSum_config] at hq
    by_cases hbad : sourceLowUnionParameter n (sourceConfigDegrees n B) < 1-Real.exp (-(4/5 : ℝ))
    · have hb : (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
          (∑ x : Molecule n, truncatedBandValue (sourceLowBandLower n) (sourceShrinkingLower n) (B x)) <
          (4/5 : ℝ) := by
        by_contra h
        have he := Real.exp_le_exp.mpr (neg_le_neg (le_of_not_gt h))
        linarith only [hq, hbad, he]
      simp only [if_pos hbad, if_pos hb, mul_one, le_refl]
    · simp only [if_neg hbad, mul_zero]
      split_ifs <;> linarith only [hw]

theorem sourceHighUnionFailureMass_tendsto_zero :
    Tendsto sourceHighUnionFailureMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    sourceHighBandCoverageFailureMass_tendsto_zero
  · filter_upwards [sourceLowBand_eventual_bounds] with n hb
    exact (sourceHighUnionFailureMass_le n hb.1 hb.2.2.1).1
  · filter_upwards [sourceLowBand_eventual_bounds] with n hb
    exact (sourceHighUnionFailureMass_le n hb.1 hb.2.2.1).2

theorem sourceLowUnionFailureMass_tendsto_zero :
    Tendsto sourceLowUnionFailureMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    sourceLowBandIntensityFailureMass_tendsto_zero
  · filter_upwards [sourceShrinkingBand_eventual_bounds] with n hb
    exact (sourceLowUnionFailureMass_le n hb.1 hb.2.2.2.2.1).1
  · filter_upwards [sourceShrinkingBand_eventual_bounds] with n hb
    exact (sourceLowUnionFailureMass_le n hb.1 hb.2.2.2.2.1).2

end
end PowerLawSmallRAF
