import proofs.PowerLawSmallRAF.CoverageProfile
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.Data.Nat.Choose.Sum

namespace PowerLawSmallRAF

/-- The total weight of outcomes in which every target reaction is covered,
written as the intersection of the complements of its miss events. -/
noncomputable def allCoveredWeight {I Ω : Type*}
    [DecidableEq I] [Fintype Ω] [DecidableEq Ω]
    (targets : Finset I) (miss : I → Finset Ω) (weight : Ω → ℝ) : ℝ :=
  ∑ ω ∈ targets.inf (fun i => (miss i)ᶜ), weight ω

/-- The scalar coverage kernel from the campaign guide. -/
noncomputable def coverageInclusionExclusion
    (u : Nat → ℝ) (r q : Nat) : ℝ :=
  ∑ j ∈ Finset.range (r + 1),
    (-1 : ℝ) ^ j * (Nat.choose r j : ℝ) * u j ^ q

/-- Exact finite inclusion-exclusion.  Independence of the `q` molecule
choices is isolated in `hintersection`: every `j`-fold joint miss has weight
`u j ^ q`. -/
theorem allCoveredWeight_eq_coverageInclusionExclusion
    {I Ω : Type*} [DecidableEq I] [Fintype Ω] [DecidableEq Ω]
    (targets : Finset I) (miss : I → Finset Ω) (weight : Ω → ℝ)
    (u : Nat → ℝ) (q : Nat)
    (hintersection : ∀ t ∈ targets.powerset,
      (∑ ω ∈ t.inf miss, weight ω) = u t.card ^ q) :
    allCoveredWeight targets miss weight =
      coverageInclusionExclusion u targets.card q := by
  rw [allCoveredWeight, Finset.inclusion_exclusion_sum_inf_compl]
  calc
    (∑ t ∈ targets.powerset,
        (-1 : ℤ) ^ t.card • ∑ ω ∈ t.inf miss, weight ω) =
        ∑ t ∈ targets.powerset,
          (-1 : ℝ) ^ t.card * u t.card ^ q := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [hintersection t ht]
      simp
    _ = ∑ j ∈ Finset.range (targets.card + 1),
        targets.card.choose j • ((-1 : ℝ) ^ j * u j ^ q) := by
      exact Finset.sum_powerset_apply_card
        (fun j => (-1 : ℝ) ^ j * u j ^ q)
    _ = coverageInclusionExclusion u targets.card q := by
      rw [coverageInclusionExclusion]
      apply Finset.sum_congr rfl
      intro j _hj
      simp only [nsmul_eq_mul]
      ring

/-- Capped-Zipf specialization of the exact coverage kernel. -/
noncomputable def powerLawCoverageProbability
    (a : ℝ) (R r q : Nat) : ℝ :=
  coverageInclusionExclusion
    (fun j => coverageMissProfile (cappedZipfDegreeMass a R) R j) r q

end PowerLawSmallRAF
