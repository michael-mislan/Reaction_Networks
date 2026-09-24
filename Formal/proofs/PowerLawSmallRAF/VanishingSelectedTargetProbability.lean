import proofs.PowerLawSmallRAF.SelectedBoundedTargetAverage
import proofs.PowerLawSmallRAF.VanishingTargetError
import proofs.PowerLawSmallRAF.VanishingSeedRetainedLaw

namespace PowerLawSmallRAF
open Classical RAF.Polymer Filter Topology
noncomputable section

theorem vanishingLowRows_weight_nonneg (n : Nat) (hn : 4 ≤ n) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) :
    0 ≤ bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A := by
  apply Finset.prod_nonneg
  intro x _
  exact bernoulliSubsetRowWeight_nonneg (sourceVanishingLowOwnerParameter_bounds n hn d x).1
    (sourceVanishingLowOwnerParameter_bounds n hn d x).2 (A x)

theorem vanishingLowRows_weight_sum (n : Nat) (d : SourceDegreeConfig n) :
    (∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A) = 1 := by
  unfold bernoulliRowsWeight
  rw [← Fintype.prod_sum (fun (x : SourceLowOwnerGroup n d) (A : Finset (Reaction n)) =>
    bernoulliSubsetRowWeight (sourceVanishingLowOwnerParameter n d x) A)]
  simp only [sum_bernoulliSubsetRowWeight,Finset.prod_const_one]

def sourceVanishingSelectedTargetMass (n m : Nat) (K : ℝ)
    (W : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset LigationWord)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
      if targetSetAdmissible n m K (W d A) then
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n) (W d A) (T d A)
      else 0

theorem sourceVanishingSelectedTargetMass_bound (n m : Nat) (K E : ℝ) (hn : 4 ≤ n) (hE : 0 ≤ E)
    (W : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset LigationWord)
    (T : (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n))
    (hbound : ∀ q : ℝ, targetIntensity n ≤ q → q ≤ 1 → ∀ V : Finset LigationWord,
      targetSetAdmissible n m K V → ∀ P : Finset (Reaction n) → Finset (Reaction n),
      sourceBoundedTargetsFailureMass q n (targetNucleusLength n) V P ≤ E) :
    0 ≤ sourceVanishingSelectedTargetMass n m K W T ∧
      sourceVanishingSelectedTargetMass n m K W T ≤ sourceHighUnionFailureMass n+E := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  have hp (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :
      0 ≤ (if targetSetAdmissible n m K (W d A) then
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n) (W d A) (T d A) else 0) ∧
      (if targetSetAdmissible n m K (W d A) then
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n) (W d A) (T d A) else 0) ≤
        (if sourceHighUnionParameter n d < targetIntensity n then 1 else 0)+E := by
    have hq := (sourceBandUnionParameter_bounds n hn d).2
    have hm := source_bounded_failure_mass_bounds hq.1 hq.2 n (targetNucleusLength n) (W d A) (T d A)
    constructor
    · split_ifs <;> linarith only [hm.1]
    · by_cases hv : targetSetAdmissible n m K (W d A)
      · rw [if_pos hv]
        by_cases hb : sourceHighUnionParameter n d < targetIntensity n
        · rw [if_pos hb]
          linarith only [hm.2,hE]
        · rw [if_neg hb,zero_add]
          exact hbound _ (le_of_not_gt hb) hq.2 _ hv _
      · rw [if_neg hv]
        split_ifs <;> linarith only [hE]
  constructor
  · apply Finset.sum_nonneg
    intro d _
    apply mul_nonneg (sourceDegreeWeight_nonneg _ _ ha d)
    apply Finset.sum_nonneg
    intro A _
    exact mul_nonneg (vanishingLowRows_weight_nonneg n hn d A) (hp d A).1
  · unfold sourceVanishingSelectedTargetMass
    calc
      _ ≤ ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
          ((if sourceHighUnionParameter n d < targetIntensity n then 1 else 0)+E) := by
        apply Finset.sum_le_sum
        intro d _
        apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
        calc
          _ ≤ ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
              ((if sourceHighUnionParameter n d < targetIntensity n then 1 else 0)+E) :=
            Finset.sum_le_sum (fun A _ => mul_le_mul_of_nonneg_left (hp d A).2 (vanishingLowRows_weight_nonneg n hn d A))
          _ = _ := by rw [← Finset.sum_mul,vanishingLowRows_weight_sum,one_mul]
      _ = sourceHighUnionFailureMass n+E := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib,← Finset.sum_mul,sourceDegreeWeight_sum_eq_one _ n ha hn,one_mul]
        rfl

/-- Targets may depend on all retained low rows, but the high field is
averaged only after that selection. Fixed seed owners are included in C. -/
theorem sourceVanishingSelectedLowTargets_tendsto_zero (C : Nat)
    (W : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset LigationWord)
    (T : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) :
    Tendsto (fun n => sourceVanishingSelectedTargetMass n (sourceVanishingLowOwnerLength n)
      ((C : ℝ)+2^(targetNucleusLength n+1)) (W n) (T n)) atTop (𝓝 0) := by
  have hb := sourceHighUnionFailureMass_tendsto_zero.add (vanishingLowTargetError_tendsto_zero C)
  simp only [add_zero] at hb
  have he : ∀ᶠ n : Nat in atTop,
      0 ≤ sourceVanishingSelectedTargetMass n (sourceVanishingLowOwnerLength n)
        ((C : ℝ)+2^(targetNucleusLength n+1)) (W n) (T n) ∧
      sourceVanishingSelectedTargetMass n (sourceVanishingLowOwnerLength n)
        ((C : ℝ)+2^(targetNucleusLength n+1)) (W n) (T n) ≤
          sourceHighUnionFailureMass n+vanishingLowTargetError C n := by
    filter_upwards [eventually_ge_atTop 4,source_bounded_vanishing_low_uniform_bound] with n hn hu
    apply sourceVanishingSelectedTargetMass_bound _ _ _ _ hn (by unfold vanishingLowTargetError; positivity) _ _
    intro q hpq hq V hV P
    exact hu C q hpq hq V hV.1 hV.2 P
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)

/-- The unchanged high-target estimate also survives averaging over the
new low rows and an arbitrary low-dependent seed base. -/
theorem sourceVanishingSelectedHighTargets_tendsto_zero
    (W : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset LigationWord)
    (T : (n : Nat) → (d : SourceDegreeConfig n) → RetainedSourceLowRows n d → Finset (Reaction n) → Finset (Reaction n)) :
    Tendsto (fun n => sourceVanishingSelectedTargetMass n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*2^shrinkingBandWidth n) (W n) (T n)) atTop (𝓝 0) := by
  have hb := sourceHighUnionFailureMass_tendsto_zero.add highTargetError_tendsto_zero
  simp only [add_zero] at hb
  have he : ∀ᶠ n : Nat in atTop,
      0 ≤ sourceVanishingSelectedTargetMass n (n-2*shrinkingBandWidth n)
        ((n : ℝ)^3*2^shrinkingBandWidth n) (W n) (T n) ∧
      sourceVanishingSelectedTargetMass n (n-2*shrinkingBandWidth n)
        ((n : ℝ)^3*2^shrinkingBandWidth n) (W n) (T n) ≤ sourceHighUnionFailureMass n+highTargetError n := by
    filter_upwards [eventually_ge_atTop 4,source_bounded_high_uniform_bound] with n hn hu
    apply sourceVanishingSelectedTargetMass_bound _ _ _ _ hn (by unfold highTargetError; positivity) _ _
    intro q hpq hq V hV P
    exact hu q hpq hq V hV.1 hV.2 P
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (he.mono fun _ h => h.1) (he.mono fun _ h => h.2)

end
end PowerLawSmallRAF
