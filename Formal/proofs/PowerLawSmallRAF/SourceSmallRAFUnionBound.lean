import proofs.PowerLawSmallRAF.SourcePowerLawTraceProbability

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

noncomputable def sourceBoundedRevRAFProbability
    (a : ℝ) (n m : Nat) : ℝ := by
  classical
  exact ∑ config : SourceMoleculeFibreConfig n,
    if ∃ S : Finset (Reaction n),
        S.card ≤ m ∧ IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S then
      sourcePowerLawConfigWeight a n config else 0

noncomputable def sourceSmallRevRAFUnionBound
    (a : ℝ) (n m : Nat) : ℝ :=
  ∑ r ∈ Finset.Icc 1 m,
    ∑ S ∈ sourceFoodGeneratedSupports n r,
      sourceFixedRevRAFMass a n S

theorem sourceFixedRevRAFMass_nonneg
    (a : ℝ) (n : Nat) (ha : 1 < a) (S : Finset (Reaction n)) :
    0 ≤ sourceFixedRevRAFMass a n S := by
  classical
  rw [sourceFixedRevRAFMass]
  exact Finset.sum_nonneg fun config hconfig => by
    by_cases hraf : IsRevRAF (binaryPolymerCRS n 2)
        (sourceCatalysisOfConfig config) S
    · simp [hraf, sourcePowerLawConfigWeight_nonneg a n ha config]
    · simp [hraf]

/-- The probability of some nonempty reversible RAF with at most `m`
reactions is bounded by the sum of the fixed-support RAF masses. -/
theorem sourceBoundedRevRAFProbability_le_unionBound
    (a : ℝ) (n m : Nat) (ha : 1 < a) :
    sourceBoundedRevRAFProbability a n m ≤
      sourceSmallRevRAFUnionBound a n m := by
  classical
  rw [sourceBoundedRevRAFProbability, sourceSmallRevRAFUnionBound]
  have hpoint : ∀ config : SourceMoleculeFibreConfig n,
      (if ∃ S : Finset (Reaction n),
          S.card ≤ m ∧ IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ r ∈ Finset.Icc 1 m,
        ∑ S ∈ sourceFoodGeneratedSupports n r,
          if IsRevRAF (binaryPolymerCRS n 2)
              (sourceCatalysisOfConfig config) S then
            sourcePowerLawConfigWeight a n config else 0 := by
    intro config
    by_cases hex : ∃ S : Finset (Reaction n),
        S.card ≤ m ∧ IsRevRAF (binaryPolymerCRS n 2)
          (sourceCatalysisOfConfig config) S
    · have hevent := hex
      obtain ⟨S, hSm, hraf⟩ := hex
      have hSpos : 1 ≤ S.card := Finset.one_le_card.mpr hraf.1
      have hrmem : S.card ∈ Finset.Icc 1 m :=
        Finset.mem_Icc.mpr ⟨hSpos, hSm⟩
      have hSmem : S ∈ sourceFoodGeneratedSupports n S.card := by
        simp [sourceFoodGeneratedSupports, hraf.2.1]
      simp only [if_pos hevent]
      have hsupport := Finset.single_le_sum
        (s := sourceFoodGeneratedSupports n S.card)
        (f := fun T => if IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) T then
          sourcePowerLawConfigWeight a n config else 0)
        (fun T hT => by
          by_cases hTraf : IsRevRAF (binaryPolymerCRS n 2)
              (sourceCatalysisOfConfig config) T
          · simp [hTraf, sourcePowerLawConfigWeight_nonneg a n ha config]
          · simp [hTraf]) hSmem
      have houter := Finset.single_le_sum
        (s := Finset.Icc 1 m)
        (f := fun r => ∑ T ∈ sourceFoodGeneratedSupports n r,
          if IsRevRAF (binaryPolymerCRS n 2)
              (sourceCatalysisOfConfig config) T then
            sourcePowerLawConfigWeight a n config else 0)
        (fun r hr => Finset.sum_nonneg fun T hT => by
          by_cases hTraf : IsRevRAF (binaryPolymerCRS n 2)
              (sourceCatalysisOfConfig config) T
          · simp [hTraf, sourcePowerLawConfigWeight_nonneg a n ha config]
          · simp [hTraf]) hrmem
      have hsupport' : sourcePowerLawConfigWeight a n config ≤
          ∑ T ∈ sourceFoodGeneratedSupports n S.card,
            if IsRevRAF (binaryPolymerCRS n 2)
                (sourceCatalysisOfConfig config) T then
              sourcePowerLawConfigWeight a n config else 0 := by
        simpa [hraf] using hsupport
      exact hsupport'.trans houter
    · simp only [if_neg hex]
      exact Finset.sum_nonneg fun r hr => Finset.sum_nonneg fun S hS => by
        by_cases hraf : IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) S
        · simp [hraf, sourcePowerLawConfigWeight_nonneg a n ha config]
        · simp [hraf]
  calc
    (∑ config : SourceMoleculeFibreConfig n,
      if ∃ S : Finset (Reaction n),
          S.card ≤ m ∧ IsRevRAF (binaryPolymerCRS n 2)
            (sourceCatalysisOfConfig config) S then
        sourcePowerLawConfigWeight a n config else 0) ≤
      ∑ config : SourceMoleculeFibreConfig n,
        ∑ r ∈ Finset.Icc 1 m,
          ∑ S ∈ sourceFoodGeneratedSupports n r,
            if IsRevRAF (binaryPolymerCRS n 2)
                (sourceCatalysisOfConfig config) S then
              sourcePowerLawConfigWeight a n config else 0 :=
      Finset.sum_le_sum fun config hconfig => hpoint config
    _ = ∑ r ∈ Finset.Icc 1 m,
        ∑ S ∈ sourceFoodGeneratedSupports n r,
          ∑ config : SourceMoleculeFibreConfig n,
            if IsRevRAF (binaryPolymerCRS n 2)
                (sourceCatalysisOfConfig config) S then
              sourcePowerLawConfigWeight a n config else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.Icc 1 m,
        ∑ S ∈ sourceFoodGeneratedSupports n r,
          sourceFixedRevRAFMass a n S := by
      simp only [sourceFixedRevRAFMass]

theorem windowZipfMean_nonneg
    (a : ℝ) (R : Nat) (ha : 1 < a) :
    0 ≤ windowZipfMean a R := by
  have hzpos : 0 < zipfNormalizer a := by
    rw [zipfNormalizer_eq_prefix_add_tail ha 2, zipfPrefix_two ha]
    nlinarith [rpowTail_nonneg a 2]
  rw [windowZipfMean]
  apply div_nonneg _ hzpos.le
  rw [windowDirectNumerator]
  exact add_nonneg
    (Finset.sum_nonneg fun k hk =>
      mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _))
    (cappedRpowTail_nonneg a R)

theorem source_fixed_revRAF_mass_le_card_envelope
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n)) (hne : S.Nonempty)
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    sourceFixedRevRAFMass a n S ≤
      ((6 + 2 * S.card : Nat) : ℝ) *
        (windowZipfMean a (sourceReactionCount n) /
          sourceReactionCount n) := by
  obtain ⟨trace, htrace, heq, hmass⟩ :=
    source_fixed_revRAF_mass_le_trace_union a ha hn S hne hfg
  have havailable :
      (reversibleTraceAvailable (binaryFood n 2) trace).card ≤
        6 + 2 * S.card :=
    (card_reversibleTraceAvailable_le htrace).trans
      (Nat.add_le_add_right (card_binaryFood_two_le_six n) (2 * S.card))
  have hRpos : 0 < (sourceReactionCount n : ℝ) := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (hp.trans (sourceReactionCount_bounds hn).1))
  have hq : 0 ≤ windowZipfMean a (sourceReactionCount n) /
      sourceReactionCount n :=
    div_nonneg (windowZipfMean_nonneg a _ ha) hRpos.le
  exact hmass.trans (mul_le_mul_of_nonneg_right
    (by exact_mod_cast havailable) hq)

/-- Fully explicit finite first-moment bound.  The only entropy term is the
source reversible trace count `C_n^r`; arbitrary within-molecule correlations
cost only one necessary incidence per fixed support. -/
theorem sourceBoundedRevRAFProbability_le_explicit_sum
    {n m : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) (hmn : m ≤ n) :
    sourceBoundedRevRAFProbability a n m ≤
      ∑ r ∈ Finset.Icc 1 m,
        (sourceReversibleBranchCount n ^ r : ℝ) *
          ((6 + 2 * r : Nat) : ℝ) *
            (windowZipfMean a (sourceReactionCount n) /
              sourceReactionCount n) := by
  classical
  refine (sourceBoundedRevRAFProbability_le_unionBound a n m ha).trans ?_
  rw [sourceSmallRevRAFUnionBound]
  apply Finset.sum_le_sum
  intro r hr
  have hrle : r ≤ n := (Finset.mem_Icc.mp hr).2.trans hmn
  have hcount := card_sourceFoodGeneratedSupports_le (n := n) (r := r) hrle
  let B : ℝ := ((6 + 2 * r : Nat) : ℝ) *
    (windowZipfMean a (sourceReactionCount n) / sourceReactionCount n)
  have hRpos : 0 < (sourceReactionCount n : ℝ) := by
    have hp : 2 ≤ 2 ^ n := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) (by omega : 1 ≤ n)
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2)
      (hp.trans (sourceReactionCount_bounds hn).1))
  have hq : 0 ≤ windowZipfMean a (sourceReactionCount n) /
      sourceReactionCount n :=
    div_nonneg (windowZipfMean_nonneg a _ ha) hRpos.le
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg _) hq
  have hterm : ∀ S ∈ sourceFoodGeneratedSupports n r,
      sourceFixedRevRAFMass a n S ≤ B := by
    intro S hS
    have hparts := (Finset.mem_filter.mp hS).2
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hzero => by
      subst S
      have hrpos := (Finset.mem_Icc.mp hr).1
      simp only [Finset.card_empty] at hparts
      omega
    simpa [B, hparts.1] using
      source_fixed_revRAF_mass_le_card_envelope a ha hn S hne hparts.2
  have hsum := Finset.sum_le_card_nsmul
    (sourceFoodGeneratedSupports n r) (sourceFixedRevRAFMass a n) B hterm
  calc
    (∑ S ∈ sourceFoodGeneratedSupports n r,
      sourceFixedRevRAFMass a n S) ≤
        ((sourceFoodGeneratedSupports n r).card : ℝ) * B := by
      simpa [nsmul_eq_mul] using hsum
    _ ≤ (sourceReversibleBranchCount n ^ r : ℝ) * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB
    _ = (sourceReversibleBranchCount n ^ r : ℝ) *
          ((6 + 2 * r : Nat) : ℝ) *
            (windowZipfMean a (sourceReactionCount n) /
              sourceReactionCount n) := by simp [B, mul_assoc]

end PowerLawSmallRAF
