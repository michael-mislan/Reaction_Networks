import proofs.PowerLawSmallRAF.SourceTwoBandConstructionEvent

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

def sourceTwoBandGoodMass (n : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d,
      bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
        ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) H *
          (if SourceTwoBandConstructionGood n d A H then 1 else 0)

def sourceNucleusBase (n : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (_H : Finset (Reaction n)) : Finset (Reaction n) :=
  (sourceLowNucleusSelection n (targetNucleusLength n) d A).1

private theorem nucleus_indicator_le_good_add_bad (n : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (H : Finset (Reaction n)) :
    (if SourceNucleusMarked n (targetNucleusLength n) (bernoulliRowsUnion A) then (1 : ℝ) else 0) ≤
    (if SourceTwoBandConstructionGood n d A H then 1 else 0) +
    (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*(2 : ℝ)^shrinkingBandWidth n) (sourceHighTargetSet n d) then 0 else 1) +
    (if SourceBoundedTargetBad n (targetNucleusLength n) (sourceHighTargetSet n d)
      (sourceNucleusBase n d A H) H then 1 else 0) +
    (if SourceBoundedTargetBad n (targetNucleusLength n)
      (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A)
      (sourceNucleusBase n d A H) H then 1 else 0) := by
  unfold SourceTwoBandConstructionGood sourceNucleusBase
  split_ifs <;> simp_all
  norm_num

private theorem sourceNucleus_indicator_integrated (n : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :
    (if SourceNucleusMarked n (targetNucleusLength n) (bernoulliRowsUnion A) then (1 : ℝ) else 0) ≤
    (∑ H : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) H *
      (if SourceTwoBandConstructionGood n d A H then 1 else 0)) +
    (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*(2 : ℝ)^shrinkingBandWidth n) (sourceHighTargetSet n d) then 0 else 1) +
    sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
      (sourceHighTargetSet n d) (sourceNucleusBase n d A) +
    sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
      (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) (sourceNucleusBase n d A) := by
  have hq := (sourceBandUnionParameter_bounds n hn d).2
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Reaction n))))
    (fun H _ => mul_le_mul_of_nonneg_left (nucleus_indicator_le_good_add_bad n d A H)
      (bernoulliSubsetRowWeight_nonneg hq.1 hq.2 H))
  simp only [mul_add,Finset.sum_add_distrib] at h
  simp only [← Finset.sum_mul,sum_bernoulliSubsetRowWeight,one_mul] at h
  simpa only [SourceBoundedTargetBad,sourceBoundedTargetsFailureMass,mul_ite,mul_one,mul_zero] using h

/-- Positive nucleus mass pays only the already identified exceptional
events. No independence between nucleus and target success is used. -/
theorem sourceLowNucleusMass_le_good_add_errors (n : Nat) (hn : 4 ≤ n) :
    sourceLowRowsNucleusMass n (targetNucleusLength n) ≤ sourceTwoBandGoodMass n +
      sourceHighTargetInvalidMass n +
      sourceActualBoundedHighTargetFailureMass n (sourceNucleusBase n) +
      sourceActualBoundedLowTargetFailureMass n (sourceNucleusBase n) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (SourceDegreeConfig n)))
    (fun d _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := (Finset.univ : Finset (RetainedSourceLowRows n d)))
        (fun A _ => mul_le_mul_of_nonneg_left (sourceNucleus_indicator_integrated n hn d A)
          (sourceRetainedLowRowWeight_nonneg n hn d A)))
      (sourceDegreeWeight_nonneg _ _ ha d))
  simpa only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,sourceRetainedLowRowWeight_sum,
    one_mul,sourceLowRowsNucleusMass,sourceTwoBandGoodMass,sourceHighTargetInvalidMass,
    sourceActualBoundedHighTargetFailureMass,sourceActualBoundedLowTargetFailureMass] using h

theorem sourceTwoBandGoodMass_eq_full_rows (n : Nat) :
    sourceTwoBandGoodMass n =
    ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
      ∑ config : SourceMoleculeFibreConfig n,
        bernoulliRowsWeight (sourceBandBernoulliParameter n d) config *
          (if SourceTwoBandConstructionGood n d (fun x => config x.val)
            (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val)) then 1 else 0) := by
  unfold sourceTwoBandGoodMass
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact (sourceRetainedLowRows_high_union_expectation n d
    (fun A H => if SourceTwoBandConstructionGood n d A H then 1 else 0)).symm

theorem sourceTwoBandGoodMass_le_auxiliary (n : Nat) (hn : 4 ≤ n)
    (hL : 3 ≤ targetNucleusLength n) (hLn : targetNucleusLength n ≤ n) :
    sourceTwoBandGoodMass n ≤ sourceTwoBandAuxiliaryRAFMass n (sourceTwoBandConstructionBudget n) := by
  rw [sourceTwoBandGoodMass_eq_full_rows]
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
  apply Finset.sum_le_sum
  intro config _
  have hw : 0 ≤ bernoulliRowsWeight (sourceBandBernoulliParameter n d) config := by
    apply Finset.prod_nonneg
    intro x _
    exact bernoulliSubsetRowWeight_nonneg (sourceBandBernoulliParameter_bounds n hn d x).1
      (sourceBandBernoulliParameter_bounds n hn d x).2.1 _
  by_cases hg : SourceTwoBandConstructionGood n d (fun x => config x.val)
      (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val))
  · have hr := sourceTwoBandConstructionGood_implies_boundedRAF n hL hLn d config hg
    simp only [if_pos hg,if_pos hr,mul_one,le_refl]
  · simp only [if_neg hg,mul_zero]
    split_ifs <;> linarith only [hw]

end
end PowerLawSmallRAF
