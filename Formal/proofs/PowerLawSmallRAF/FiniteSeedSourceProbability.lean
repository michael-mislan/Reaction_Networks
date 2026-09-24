import proofs.PowerLawSmallRAF.FiniteSeedGoodProbability

namespace PowerLawSmallRAF
open Classical RAF RAF.Polymer RAF.Concrete Filter Topology
noncomputable section

theorem sourceVanishingRetainedRows_high_union_expectation (n : Nat) (d : SourceDegreeConfig n)
    (F : RetainedSourceLowRows n d → Finset (Reaction n) → ℝ) :
    (∑ B : SourceMoleculeFibreConfig n, bernoulliRowsWeight (sourceVanishingBandParameter n d) B *
      F (fun x => B x.val) (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => B x.val))) =
      ∑ A : RetainedSourceLowRows n d, bernoulliRowsWeight (sourceVanishingLowOwnerParameter n d) A *
        ∑ H : Finset (Reaction n), bernoulliSubsetRowWeight (sourceHighUnionParameter n d) H * F A H := by
  have hh := bernoulliRows_retained_low_high_union_expectation (sourceVanishingBandParameter n d)
    (fun x => (d x).val < sourceShrinkingLower n) F
  simpa only [sourceVanishingBandParameter_low,sourceVanishingBandParameter_high,sourceHighUnionParameter] using hh

theorem sourceFiniteSeedGoodMass_le_auxiliary (n N m : Nat) (hn : 4 ≤ n) (hNn : N ≤ n)
    (hL : 3 ≤ targetNucleusLength n) (hLn : targetNucleusLength n ≤ n) :
    sourceFiniteSeedGoodMass n N m ≤ sourceVanishingBandAuxiliaryRAFMass n (sourceFiniteSeedConstructionBudget N n) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have ha : 1 < 2-2/(n : ℝ) := by
    have hh := (div_lt_one hn0).mpr (show (2 : ℝ)<n by exact_mod_cast (show 2<n by omega))
    linarith
  unfold sourceFiniteSeedGoodMass sourceVanishingBandAuxiliaryRAFMass
  apply Finset.sum_le_sum
  intro d _
  apply mul_le_mul_of_nonneg_left _ (sourceDegreeWeight_nonneg _ _ ha d)
  rw [← sourceVanishingRetainedRows_high_union_expectation n d
    (fun A H => if SourceFiniteSeedConstructionGood n N m d A H then 1 else 0)]
  apply Finset.sum_le_sum
  intro config _
  have hw : 0 ≤ bernoulliRowsWeight (sourceVanishingBandParameter n d) config := by
    apply Finset.prod_nonneg
    intro x _
    exact bernoulliSubsetRowWeight_nonneg (sourceVanishingBandParameter_bounds n hn d x).1
      (sourceVanishingBandParameter_bounds n hn d x).2 _
  by_cases hg : SourceFiniteSeedConstructionGood n N m d (fun x => config x.val)
      (bernoulliRowsUnion (fun x : SourceHighOwnerGroup n d => config x.val))
  · have hr := sourceFiniteSeedConstructionGood_implies_boundedRAF n N m hNn hL hLn d config hg
    simp only [if_pos hg,if_pos hr,mul_one,le_refl]
  · simp only [if_neg hg,mul_zero]
    split_ifs <;> linarith only [hw]

def sourceFiniteSeedTotalError (N m n : Nat) : ℝ :=
  sourceHighTargetInvalidMass n + sourceVanishingLowShortDegreeMass n +
    sourceFiniteSeedHighFailure N m n + sourceFiniteSeedLowFailure N m n + sourceVanishingRowErrorEnvelope n

theorem sourceFiniteSeedTotalError_tendsto_zero (N m : Nat) :
    Tendsto (sourceFiniteSeedTotalError N m) atTop (𝓝 0) := by
  have hh := (((sourceHighTargetInvalidMass_tendsto_zero.add sourceVanishingLowShortDegreeMass_tendsto_zero).add
    (sourceFiniteSeedHighFailure_tendsto_zero N m)).add (sourceFiniteSeedLowFailure_tendsto_zero N m)).add
      sourceVanishingRowErrorEnvelope_tendsto_zero
  simpa only [add_zero,sourceFiniteSeedTotalError] using hh

/-- The finite seed probability transfers all the way to actual source
RAFs, losing only the five explicitly vanishing exceptional masses. -/
theorem sourceFiniteSeedMass_eventually_le_source (N m : Nat) :
    ∀ᶠ n : Nat in atTop, sourceVanishingLowRowsSeedMass n N m (targetNucleusLength n) ≤
      sourceBoundedRevRAFProbability (2-2/(n : ℝ)) n (sourceFiniteSeedConstructionBudget N n) +
        sourceFiniteSeedTotalError N m n := by
  filter_upwards [eventually_ge_atTop 4,eventually_ge_atTop N,targetUnion_eventual_conditions,
    sourceVanishingBandAuxiliaryRAFMass_eventually_le_source] with n hn hN hcond hcouple
  have hLn : targetNucleusLength n ≤ n := hcond.2.2.2.1.trans (Nat.div_le_self _ _)
  have hL : 3 ≤ targetNucleusLength n := by have hh := hcond.2.2.1; omega
  have h1 := sourceFiniteSeedMass_le_good_add_errors n N m hn
  have h2 := sourceFiniteSeedGoodMass_le_auxiliary n N m hn hN hL hLn
  have h3 := hcouple (sourceFiniteSeedConstructionBudget N n)
  unfold sourceFiniteSeedTotalError
  linarith

end
end PowerLawSmallRAF
