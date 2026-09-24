import proofs.PowerLawSmallRAF.SelectedBoundedTargetAverage
import proofs.PowerLawSmallRAF.HighOwnerTargetSet
import proofs.PowerLawSmallRAF.SourceLowTargetInvalidMass

namespace PowerLawSmallRAF
open RAF.Polymer Filter Topology
noncomputable section
attribute [local instance] Classical.propDecidable

/-- No admissibility guard: every actual high-owner label is a target. -/
def sourceActualBoundedHighTargetFailureMass (n : Nat)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
      sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
        (sourceHighTargetSet n d) (T d A)

theorem sourceActualBoundedHighTargetFailureMass_bound (n : Nat) (hn : 4 ≤ n)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) :
    0 ≤ sourceActualBoundedHighTargetFailureMass n T ∧ sourceActualBoundedHighTargetFailureMass n T ≤
      sourceSelectedBoundedTargetMass n (n-2*shrinkingBandWidth n) ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n))
        (fun d _ => sourceHighTargetSet n d) T + sourceHighTargetInvalidMass n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  let V := fun d => targetSetAdmissible n (n-2*shrinkingBandWidth n)
    ((n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)) (sourceHighTargetSet n d)
  have hw (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :
      0 ≤ bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A := by
    apply Finset.prod_nonneg
    intro x _
    exact bernoulliSubsetRowWeight_nonneg (sourceBandBernoulliParameter_bounds n hn d x.val).1
      (sourceBandBernoulliParameter_bounds n hn d x.val).2.1 (A x)
  have hs (d : SourceDegreeConfig n) :
      (∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A) = 1 := by
    unfold bernoulliRowsWeight
    rw [← Fintype.prod_sum (fun (x : SourceLowOwnerGroup n d) (A : Finset (Reaction n)) =>
      bernoulliSubsetRowWeight (sourceBandBernoulliParameter n d x.val) A)]
    simp only [sum_bernoulliSubsetRowWeight,Finset.prod_const_one]
  have hm (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :=
    source_bounded_failure_mass_bounds (sourceBandUnionParameter_bounds n hn d).2.1
      (sourceBandUnionParameter_bounds n hn d).2.2 n (targetNucleusLength n) (sourceHighTargetSet n d) (T d A)
  constructor
  · apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d)
    exact Finset.sum_nonneg (fun A _ => mul_nonneg (hw d A) (hm d A).1)
  · unfold sourceActualBoundedHighTargetFailureMass
    calc
      _ ≤ ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
          ((∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
            if V d then sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
              (sourceHighTargetSet n d) (T d A) else 0)+(if V d then 0 else 1)) := by
        apply Finset.sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
        calc
          _ ≤ ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
              ((if V d then sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
                (sourceHighTargetSet n d) (T d A) else 0)+(if V d then 0 else 1)) := by
            apply Finset.sum_le_sum
            intro A _
            apply mul_le_mul_of_nonneg_left _ (hw d A)
            by_cases hv : V d
            · simp only [if_pos hv,add_zero,le_refl]
            · simpa only [if_neg hv,zero_add] using (hm d A).2
          _ = _ := by
            simp_rw [mul_add]
            rw [Finset.sum_add_distrib,← Finset.sum_mul,hs,one_mul]
      _ = _ := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        rfl

/-- All high-owner targets, without cardinality/length conditioning, have
vanishing joint nucleus-success/target-failure mass in the source auxiliary law. -/
theorem sourceActualBoundedHighTargetFailureMass_tendsto_zero
    (T : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n))
    :
    Tendsto (fun n => sourceActualBoundedHighTargetFailureMass n (T n)) atTop (𝓝 0) := by
  have ht := (sourceSelectedBoundedHighTargets_tendsto_zero (fun n d _ => sourceHighTargetSet n d) T).add
    sourceHighTargetInvalidMass_tendsto_zero
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceActualBoundedHighTargetFailureMass_bound n hn (T n)).1
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceActualBoundedHighTargetFailureMass_bound n hn (T n)).2

end
end PowerLawSmallRAF


namespace PowerLawSmallRAF
open RAF.Polymer Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Actual total low-owner selector, with no target admissibility guard. -/
def sourceActualBoundedLowTargetFailureMass (n : Nat)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d,
      bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
          (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) (T d A)

theorem sourceActualBoundedLowTargetFailureMass_bound (n : Nat) (hn : 4 ≤ n)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) :
    0 ≤ sourceActualBoundedLowTargetFailureMass n T ∧ sourceActualBoundedLowTargetFailureMass n T ≤
      sourceSelectedBoundedTargetMass n (n/200) ((2 : ℝ)^(targetNucleusLength n+1))
        (fun d A => sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) T +
          sourceLowTargetInvalidMass n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  let V := fun d A => targetSetAdmissible n (n/200) ((2 : ℝ)^(targetNucleusLength n+1))
    (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A)
  have hm (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :=
    source_bounded_failure_mass_bounds (sourceBandUnionParameter_bounds n hn d).2.1
      (sourceBandUnionParameter_bounds n hn d).2.2 n (targetNucleusLength n)
        (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) (T d A)
  constructor
  · apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d)
    exact Finset.sum_nonneg (fun A _ =>
      mul_nonneg (sourceRetainedLowRowWeight_nonneg n hn d A) (hm d A).1)
  · unfold sourceActualBoundedLowTargetFailureMass
    calc
      _ ≤ ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
          ∑ A : RetainedSourceLowRows n d,
            bernoulliRowsWeight (fun x => sourceBandBernoulliParameter n d x.val) A *
              ((if V d A then sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d)
                n (targetNucleusLength n) (sourceLowNucleusOwnerWords n (targetNucleusLength n) d A)
                  (T d A) else 0) + (if V d A then 0 else 1)) := by
        apply Finset.sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
        apply Finset.sum_le_sum
        intro A _
        apply mul_le_mul_of_nonneg_left _ (sourceRetainedLowRowWeight_nonneg n hn d A)
        by_cases hv : V d A
        · simp only [if_pos hv,add_zero,le_refl]
        · simpa only [if_neg hv,zero_add] using (hm d A).2
      _ = _ := by
        simp_rw [mul_add,Finset.sum_add_distrib]
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        rfl

/-- The joint nucleus-success/selected-low-target-failure mass tends to
zero without cardinality or length conditioning on the selected targets. -/
theorem sourceActualBoundedLowTargetFailureMass_tendsto_zero
    (T : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n))
    :
    Tendsto (fun n => sourceActualBoundedLowTargetFailureMass n (T n)) atTop (𝓝 0) := by
  have ht := (sourceSelectedBoundedLowTargets_tendsto_zero
    (fun n d A => sourceLowNucleusOwnerWords n (targetNucleusLength n) d A) T).add
      sourceLowTargetInvalidMass_tendsto_zero
  simp only [add_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceActualBoundedLowTargetFailureMass_bound n hn (T n)).1
  · filter_upwards [eventually_ge_atTop 4] with n hn
    exact (sourceActualBoundedLowTargetFailureMass_bound n hn (T n)).2

end
end PowerLawSmallRAF

