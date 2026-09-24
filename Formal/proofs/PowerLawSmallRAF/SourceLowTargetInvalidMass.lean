import proofs.PowerLawSmallRAF.SourceLowOwnerAdmissibility
import proofs.PowerLawSmallRAF.SourceShortOwnerExclusions

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceRetainedLowRowWeight_nonneg (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :
    0 ≤ bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A := by
  apply Finset.prod_nonneg
  intro x _
  exact bernoulliSubsetRowWeight_nonneg (sourceBandBernoulliParameter_bounds n hn d x.val).1
    (sourceBandBernoulliParameter_bounds n hn d x.val).2.1 (A x)

theorem sourceRetainedLowRowWeight_sum (n : Nat) (d : SourceDegreeConfig n) :
    (∑ A : RetainedSourceLowRows n d,
      bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A) = 1 := by
  unfold bernoulliRowsWeight
  rw [← Fintype.prod_sum (fun (x : SourceLowOwnerGroup n d) (A : Finset (Reaction n)) =>
    bernoulliSubsetRowWeight (sourceBandBernoulliParameter n d x.val) A)]
  simp only [sum_bernoulliSubsetRowWeight,Finset.prod_const_one]

def sourceLowShortDegreeMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    (if ∃ x : Molecule n, x.1.val < n/200 ∧ sourceLowBandLower n ≤ (d x).val then 1 else 0)

theorem sourceLowShortDegreeMass_eq (n : Nat) : sourceLowShortDegreeMass n =
    sourceShortOwnerFailureMass (2-2/(n : ℝ)) n (n/200) (sourceLowBandLower n) := by
  unfold sourceLowShortDegreeMass
  rw [← sourceDegreeStatistics_expectation (2-2/(n : ℝ)) n
    (fun d => if ∃ x : Molecule n, x.1.val < n/200 ∧ sourceLowBandLower n ≤ (d x).val then 1 else 0)]
  unfold sourceShortOwnerFailureMass
  apply Finset.sum_congr rfl
  intro B _
  simp only [sourceConfigDegrees,mul_ite,mul_one,mul_zero]

def sourceLowTargetInvalidMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d,
      bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
        (if targetSetAdmissible n (n/200) ((2 : ℝ)^(targetNucleusLength n+1))
          (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) then 0 else 1)

theorem sourceLowTargetInvalidMass_bound (n : Nat) (hn : 4 ≤ n) :
    0 ≤ sourceLowTargetInvalidMass n ∧ sourceLowTargetInvalidMass n ≤ sourceLowShortDegreeMass n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  constructor
  · apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d)
    apply Finset.sum_nonneg
    intro A _
    exact mul_nonneg (sourceRetainedLowRowWeight_nonneg n hn d A) (by split_ifs <;> norm_num)
  · unfold sourceLowTargetInvalidMass sourceLowShortDegreeMass
    apply Finset.sum_le_sum
    intro d _
    apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
    calc
      _ ≤ ∑ A : RetainedSourceLowRows n d,
          bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
            (if ∃ x : Molecule n, x.1.val < n/200 ∧ sourceLowBandLower n ≤ (d x).val then 1 else 0) := by
        apply Finset.sum_le_sum
        intro A _
        have hw := sourceRetainedLowRowWeight_nonneg n hn d A
        by_cases hz : bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A = 0
        · simp only [hz,zero_mul,le_refl]
        · by_cases hs : ∃ x : Molecule n, x.1.val < n/200 ∧ sourceLowBandLower n ≤ (d x).val
          · rw [if_pos hs]
            split_ifs <;> nlinarith
          · have hv := sourceLowNucleusOwnerWords_admissible n (targetNucleusLength n) (n/200) hn d A hz hs
            simp only [if_pos hv,if_neg hs,mul_zero,le_refl]
      _ = _ := by rw [← Finset.sum_mul,sourceRetainedLowRowWeight_sum,one_mul]

theorem sourceLowTargetInvalidMass_tendsto_zero :
    Tendsto sourceLowTargetInvalidMass atTop (𝓝 0) := by
  have ht : Tendsto sourceLowShortDegreeMass atTop (𝓝 0) := by
    change Tendsto (fun n => sourceLowShortDegreeMass n) atTop (𝓝 0)
    simp_rw [sourceLowShortDegreeMass_eq]
    exact sourceLowShortOwnerFailureMass_tendsto_zero
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceLowTargetInvalidMass_bound n hn).1
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceLowTargetInvalidMass_bound n hn).2

end
end PowerLawSmallRAF
