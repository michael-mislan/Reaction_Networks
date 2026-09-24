import proofs.PowerLawSmallRAF.FiniteSeedRAFAssembly
import proofs.PowerLawSmallRAF.VanishingSelectedTargetProbability

namespace PowerLawSmallRAF
open Classical RAF.Polymer Filter Topology
noncomputable section

def sourceFiniteSeedBase (n N m : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (_H : Finset (Reaction n)) : Finset (Reaction n) :=
  (sourceFiniteSeedSelection n N m (targetNucleusLength n) d A).1

def sourceFiniteSeedGoodMass (n N m : Nat) : ℝ :=
  ∑ d : SourceDegreeConfig n, sourceDegreeWeight (2-2/(n : ℝ)) n d *
    ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
      ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) H *
        (if SourceFiniteSeedConstructionGood n N m d A H then 1 else 0)

def sourceFiniteSeedHighFailure (N m n : Nat) : ℝ :=
  sourceVanishingSelectedTargetMass n (n-2*shrinkingBandWidth n)
    ((n : ℝ)^3*2^shrinkingBandWidth n) (fun d _ => sourceHighTargetSet n d) (sourceFiniteSeedBase n N m)

def sourceFiniteSeedLowFailure (N m n : Nat) : ℝ :=
  sourceVanishingSelectedTargetMass n (sourceVanishingLowOwnerLength n)
    ((Fintype.card (Reaction N) : ℝ)+2^(targetNucleusLength n+1))
    (fun d A => sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A) (sourceFiniteSeedBase n N m)

private theorem seed_indicator_le_good_errors (n N m : Nat) (d : SourceDegreeConfig n)
    (A : RetainedSourceLowRows n d) (H : Finset (Reaction n))
    (hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A ≠ 0) :
    (if sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
      SourceAboveSeedMarked n m (targetNucleusLength n) (bernoulliRowsUnion A) then (1 : ℝ) else 0) ≤
    (if SourceFiniteSeedConstructionGood n N m d A H then 1 else 0) +
    (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*2^shrinkingBandWidth n) (sourceHighTargetSet n d) then 0 else 1) +
    (if ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val then 1 else 0) +
    (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
      ((n : ℝ)^3*2^shrinkingBandWidth n) (sourceHighTargetSet n d) then
      (if SourceBoundedTargetBad n (targetNucleusLength n) (sourceHighTargetSet n d)
        (sourceFiniteSeedBase n N m d A H) H then 1 else 0) else 0) +
    (if targetSetAdmissible n (sourceVanishingLowOwnerLength n)
      ((Fintype.card (Reaction N) : ℝ)+2^(targetNucleusLength n+1))
      (sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A) then
      (if SourceBoundedTargetBad n (targetNucleusLength n)
        (sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A)
        (sourceFiniteSeedBase n N m d A H) H then 1 else 0) else 0) := by
  by_cases hs : ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
      sourceVanishingLowLower n ≤ (d x).val
  · simp only [if_pos hs]
    split_ifs <;> norm_num
  · have hlow := sourceFiniteSeedOwnerWords_admissible n N m (targetNucleusLength n) d A hw hs
    simp only [if_neg hs,if_pos hlow,add_zero]
    unfold SourceFiniteSeedConstructionGood sourceFiniteSeedBase
    split_ifs <;> simp_all only [and_true,and_false,false_and,
      not_true_eq_false,not_false_eq_true] <;> norm_num

private theorem seed_integrated_low_row (n N m : Nat) (hn : 4 ≤ n)
    (d : SourceDegreeConfig n) (A : RetainedSourceLowRows n d) :
    bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
      (if sourceFiniteSeedEvent n N m (bernoulliRowsUnion A) ∧
        SourceAboveSeedMarked n m (targetNucleusLength n) (bernoulliRowsUnion A) then (1 : ℝ) else 0) ≤
    bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
      ((∑ H : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) H *
        (if SourceFiniteSeedConstructionGood n N m d A H then 1 else 0)) +
      (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
        ((n : ℝ)^3*2^shrinkingBandWidth n) (sourceHighTargetSet n d) then 0 else 1) +
      (if ∃ x : Molecule n, x.1.val < sourceVanishingLowOwnerLength n ∧
        sourceVanishingLowLower n ≤ (d x).val then 1 else 0) +
      (if targetSetAdmissible n (n-2*shrinkingBandWidth n)
        ((n : ℝ)^3*2^shrinkingBandWidth n) (sourceHighTargetSet n d) then
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
          (sourceHighTargetSet n d) (sourceFiniteSeedBase n N m d A) else 0) +
      (if targetSetAdmissible n (sourceVanishingLowOwnerLength n)
        ((Fintype.card (Reaction N) : ℝ)+2^(targetNucleusLength n+1))
        (sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A) then
        sourceBoundedTargetsFailureMass (sourceHighUnionParameter n d) n (targetNucleusLength n)
          (sourceFiniteSeedOwnerWords n N m (targetNucleusLength n) d A) (sourceFiniteSeedBase n N m d A) else 0)) := by
  by_cases hw : bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A = 0
  · simp only [hw,zero_mul,le_refl]
  · apply mul_le_mul_of_nonneg_left _ (vanishingLowRows_weight_nonneg n hn d A)
    have hq := (sourceBandUnionParameter_bounds n hn d).2
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Finset (Reaction n))))
      (fun H _ => mul_le_mul_of_nonneg_left (seed_indicator_le_good_errors n N m d A H hw)
        (bernoulliSubsetRowWeight_nonneg hq.1 hq.2 H))
    simp only [mul_add,Finset.sum_add_distrib] at hh
    simp only [← Finset.sum_mul,sum_bernoulliSubsetRowWeight,one_mul] at hh
    simpa only [SourceBoundedTargetBad,sourceBoundedTargetsFailureMass,
      mul_ite,mul_one,mul_zero,Finset.sum_ite_irrel,Finset.sum_const_zero] using hh

theorem sourceFiniteSeedMass_le_good_add_errors (n N m : Nat) (hn : 4 ≤ n) :
    sourceVanishingLowRowsSeedMass n N m (targetNucleusLength n) ≤ sourceFiniteSeedGoodMass n N m +
      sourceHighTargetInvalidMass n + sourceVanishingLowShortDegreeMass n +
      sourceFiniteSeedHighFailure N m n + sourceFiniteSeedLowFailure N m n := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (SourceDegreeConfig n)))
    (fun d _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (s := (Finset.univ : Finset (RetainedSourceLowRows n d)))
        (fun A _ => seed_integrated_low_row n N m hn d A)) (sourceDegreeWeight_nonneg _ _ ha d))
  simpa only [mul_add,Finset.sum_add_distrib,← Finset.sum_mul,vanishingLowRows_weight_sum,
    one_mul,sourceVanishingLowRowsSeedMass,sourceFiniteSeedGoodMass,sourceHighTargetInvalidMass,
    sourceVanishingLowShortDegreeMass,sourceFiniteSeedHighFailure,sourceFiniteSeedLowFailure,
    sourceVanishingSelectedTargetMass] using hh

theorem sourceFiniteSeedHighFailure_tendsto_zero (N m : Nat) :
    Tendsto (sourceFiniteSeedHighFailure N m) atTop (𝓝 0) :=
  sourceVanishingSelectedHighTargets_tendsto_zero _ _

theorem sourceFiniteSeedLowFailure_tendsto_zero (N m : Nat) :
    Tendsto (sourceFiniteSeedLowFailure N m) atTop (𝓝 0) :=
  sourceVanishingSelectedLowTargets_tendsto_zero (Fintype.card (Reaction N)) _ _

end
end PowerLawSmallRAF
