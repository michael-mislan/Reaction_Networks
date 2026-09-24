import proofs.PowerLawSmallRAF.VanishingLowProbability
import proofs.PowerLawSmallRAF.SourceBandUnionIntensity

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section

def sourceVanishingLowOwnerParameter (n : Nat) (d : SourceDegreeConfig n)
    (x : SourceLowOwnerGroup n d) : ℝ :=
  if sourceVanishingLowLower n ≤ (d x.val).val
  then sourceVanishingLowRetention n*(d x.val : ℝ)/(sourceReactionCount n : ℝ) else 0

theorem sourceVanishingLowOwnerParameter_bounds (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (x : SourceLowOwnerGroup n d) :
    0 ≤ sourceVanishingLowOwnerParameter n d x ∧ sourceVanishingLowOwnerParameter n d x ≤ 1 := by
  have hR : (0 : ℝ) < sourceReactionCount n := by
    exact_mod_cast (show 0 < sourceReactionCount n by simp [sourceReactionCount])
  have hdR : (d x.val : ℝ) ≤ sourceReactionCount n := by
    exact_mod_cast (Nat.le_of_lt_succ (d x.val).isLt).trans_eq
      (card_binaryReaction_eq_sourceReactionCount (by omega : 2 ≤ n))
  have hr := sourceVanishingLowRetention_bounds n
  unfold sourceVanishingLowOwnerParameter
  split_ifs
  · constructor
    · exact div_nonneg (mul_nonneg hr.1 (Nat.cast_nonneg _)) hR.le
    · apply (div_le_one hR).mpr
      exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hr.2).trans hdR
  · norm_num

def sourceVanishingLowDegreeIntensity (n : Nat) (d : SourceDegreeConfig n) : ℝ :=
  sourceVanishingLowRetention n/(sourceReactionCount n : ℝ)*
    sourceDegreeBandSum n d (sourceVanishingLowLower n) (sourceShrinkingLower n)

theorem sourceVanishingLowOwnerParameter_sum (n : Nat) (d : SourceDegreeConfig n) :
    (∑ x : SourceLowOwnerGroup n d, sourceVanishingLowOwnerParameter n d x) =
      sourceVanishingLowDegreeIntensity n d := by
  unfold sourceVanishingLowOwnerParameter
  rw [← Finset.sum_subtype
    (Finset.univ.filter fun x : Molecule n => (d x).val < sourceShrinkingLower n)
    (by intro x; simp)
    (fun x => if sourceVanishingLowLower n ≤ (d x).val
      then sourceVanishingLowRetention n*(d x : ℝ)/(sourceReactionCount n : ℝ) else 0)]
  rw [Finset.sum_filter,sourceVanishingLowDegreeIntensity,sourceDegreeBandSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hl : (d x).val < sourceShrinkingLower n
  · by_cases ha : sourceVanishingLowLower n ≤ (d x).val
    · simp only [hl,ha,and_self,ite_true]
      ring
    · simp [hl,ha]
  · simp [hl]

def sourceVanishingLowUnionParameter (n : Nat) (d : SourceDegreeConfig n) : ℝ :=
  bernoulliUnionParameter (sourceVanishingLowOwnerParameter n d)

theorem sourceVanishingLowUnionParameter_ge_intensity (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) :
    1-Real.exp (-sourceVanishingLowDegreeIntensity n d) ≤ sourceVanishingLowUnionParameter n d := by
  simpa only [sourceVanishingLowOwnerParameter_sum] using
    bernoulliUnionParameter_ge_exp (sourceVanishingLowOwnerParameter n d)
      (fun x => (sourceVanishingLowOwnerParameter_bounds n hn d x).2)

def sourceVanishingLowUnionFailureMass (t : ℝ) (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    (if sourceVanishingLowUnionParameter n d < 1-Real.exp (-t) then 1 else 0)

theorem sourceVanishingLowUnionFailureMass_le (t : ℝ) (n : Nat) (hn : 4 ≤ n) :
    0 ≤ sourceVanishingLowUnionFailureMass t n ∧
      sourceVanishingLowUnionFailureMass t n ≤ sourceVanishingLowIntensityFailureMass t n := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
    linarith
  constructor
  · apply Finset.sum_nonneg
    intro d _
    exact mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d) (by split_ifs <;> norm_num)
  · unfold sourceVanishingLowUnionFailureMass
    rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
      (fun d => if sourceVanishingLowUnionParameter n d < 1-Real.exp (-t) then 1 else 0)]
    unfold sourceVanishingLowIntensityFailureMass
    apply Finset.sum_le_sum
    intro B _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha B
    have hq := sourceVanishingLowUnionParameter_ge_intensity n hn (sourceConfigDegrees n B)
    have he : sourceVanishingLowDegreeIntensity n (sourceConfigDegrees n B) =
        sourceVanishingLowIntensityValue n B := rfl
    rw [he] at hq
    by_cases hb : sourceVanishingLowUnionParameter n (sourceConfigDegrees n B) < 1-Real.exp (-t)
    · have hi : sourceVanishingLowIntensityValue n B < t := by
        by_contra h
        have hexp := Real.exp_le_exp.mpr (neg_le_neg (le_of_not_gt h))
        linarith
      simp only [if_pos hb,if_pos hi,mul_one,le_refl]
    · simp only [if_neg hb,mul_zero]
      split_ifs <;> linarith

/-- After averaging actual source degrees, the conditional low union
attains every openness floor coming from an intensity below the full limit. -/
theorem sourceVanishingLowUnionFailureMass_tendsto_zero (t : ℝ) (ht : t < sourceFullIntensity) :
    Tendsto (sourceVanishingLowUnionFailureMass t) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (sourceVanishingLowIntensityFailureMass_tendsto_zero t ht)
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceVanishingLowUnionFailureMass_le t n hn).1
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceVanishingLowUnionFailureMass_le t n hn).2

end
end PowerLawSmallRAF
