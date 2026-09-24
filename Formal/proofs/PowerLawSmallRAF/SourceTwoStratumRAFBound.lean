import proofs.PowerLawSmallRAF.AssignmentRangeCounting
import proofs.PowerLawSmallRAF.SourceSmallRAFUnionBound

namespace PowerLawSmallRAF

open RAF RAF.Polymer RAF.Concrete

/-- Fixed-support RAF estimate after separating one-hub assignments from all
assignments using at least two distinct catalyst identities. -/
theorem source_fixed_revRAF_mass_le_one_add_two
    {n : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n)
    (S : Finset (Reaction n)) (hne : S.Nonempty)
    (hfg : RevFoodGenerated (binaryPolymerCRS n 2) S) :
    sourceFixedRevRAFMass a n S ≤
      ((6 + 2 * S.card : Nat) : ℝ) *
          powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 +
        (((6 + 2 * S.card) ^ S.card : Nat) : ℝ) *
          powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^ 2 := by
  classical
  obtain ⟨trace, htrace, heq, hmass⟩ :=
    source_fixed_revRAF_mass_le_exact_coverage a ha hn S hfg
  let H := reversibleTraceAvailable (binaryFood n 2) trace
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  have hkernel : powerLawCoverageProbability a (sourceReactionCount n)
      S.card H.card =
      ∑ config : SourceMoleculeFibreConfig n,
        if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0 :=
    (source_fixedCoverage_mass_eq_powerLawCoverageProbability
      a ha hn H S).symm
  have htwo := source_fixedCoverage_mass_le_one_add_two a ha hn H S hne
  have havailable : H.card ≤ 6 + 2 * S.card :=
    (card_reversibleTraceAvailable_le htrace).trans
      (Nat.add_le_add_right (card_binaryFood_two_le_six n) (2 * S.card))
  obtain ⟨r, hrS⟩ := hne
  have hp := source_gatewayHit_nonneg_le_one a ha hn r
  have hpowNat : H.card ^ S.card ≤ (6 + 2 * S.card) ^ S.card :=
    Nat.pow_le_pow_left havailable S.card
  calc
    sourceFixedRevRAFMass a n S ≤
        powerLawCoverageProbability a (sourceReactionCount n) S.card H.card := hmass
    _ = ∑ config : SourceMoleculeFibreConfig n,
        if ∀ r ∈ S, ∃ x ∈ H, r ∈ config x then
          sourcePowerLawConfigWeight a n config else 0 := hkernel
    _ ≤ (H.card : ℝ) * p + (H.card ^ S.card : Nat) * p ^ 2 := htwo
    _ ≤ ((6 + 2 * S.card : Nat) : ℝ) * p +
        (((6 + 2 * S.card) ^ S.card : Nat) : ℝ) * p ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast havailable) hp.1
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hpowNat) (sq_nonneg p)

/-- All-length finite first-moment bound retaining the one-hub/multi-hub
split.  Unlike the earlier estimate, the multi-hub term pays `p₁²`. -/
theorem sourceBoundedRevRAFProbability_le_two_stratum_sum
    {n m : Nat} (a : ℝ) (ha : 1 < a) (hn : 4 ≤ n) :
    sourceBoundedRevRAFProbability a n m ≤
      ∑ r ∈ Finset.Icc 1 m,
        (sourceReversibleBranchCountAt n r ^ r : ℝ) *
          (((6 + 2 * r : Nat) : ℝ) *
              powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 +
            (((6 + 2 * r) ^ r : Nat) : ℝ) *
              powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^ 2) := by
  classical
  refine (sourceBoundedRevRAFProbability_le_unionBound a n m ha).trans ?_
  rw [sourceSmallRevRAFUnionBound]
  apply Finset.sum_le_sum
  intro r hr
  let p := powerLawMoleculeGatewayHit a (sourceReactionCount n) 1
  let B : ℝ := ((6 + 2 * r : Nat) : ℝ) * p +
    (((6 + 2 * r) ^ r : Nat) : ℝ) * p ^ 2
  have hcount := card_sourceFoodGeneratedSupports_le_at n r
  have hB : 0 ≤ B := by
    let k : Fin n := ⟨1, by omega⟩
    let w : Word (k.val + 1) := ⟨0, by simp [k]⟩
    let s : Fin k.val := ⟨0, by simp [k]⟩
    let r0 : Reaction n := ⟨k, (w, s)⟩
    have hp : 0 ≤ p :=
      (source_gatewayHit_nonneg_le_one a ha hn r0).1
    exact add_nonneg (mul_nonneg (Nat.cast_nonneg _) hp)
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg p))
  have hterm : ∀ S ∈ sourceFoodGeneratedSupports n r,
      sourceFixedRevRAFMass a n S ≤ B := by
    intro S hS
    have hparts := (Finset.mem_filter.mp hS).2
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr fun hzero => by
      subst S
      have hrpos := (Finset.mem_Icc.mp hr).1
      simp only [Finset.card_empty] at hparts
      omega
    simpa [B, p, hparts.1] using
      source_fixed_revRAF_mass_le_one_add_two a ha hn S hne hparts.2
  have hsum := Finset.sum_le_card_nsmul
    (sourceFoodGeneratedSupports n r) (sourceFixedRevRAFMass a n) B hterm
  calc
    (∑ S ∈ sourceFoodGeneratedSupports n r,
      sourceFixedRevRAFMass a n S) ≤
        ((sourceFoodGeneratedSupports n r).card : ℝ) * B := by
      simpa [nsmul_eq_mul] using hsum
    _ ≤ (sourceReversibleBranchCountAt n r ^ r : ℝ) * B := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) hB
    _ = (sourceReversibleBranchCountAt n r ^ r : ℝ) *
          (((6 + 2 * r : Nat) : ℝ) *
              powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 +
            (((6 + 2 * r) ^ r : Nat) : ℝ) *
              powerLawMoleculeGatewayHit a (sourceReactionCount n) 1 ^ 2) := rfl

end PowerLawSmallRAF
