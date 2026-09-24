import proofs.PowerLawSmallRAF.SeedClosed

namespace PowerLawSmallRAF

/-- Conditional miss probability for one molecule of degree `d` against a
fixed set of `j` reactions among `R`. -/
noncomputable def degreeMissProbability (R j d : Nat) : ℝ :=
  (Nat.choose (R - j) d : ℝ) / Nat.choose R d

/-- The one-molecule hypergeometric miss profile for an arbitrary degree-mass
function supported on `0, ..., R - 1`. -/
noncomputable def coverageMissProfile
    (degreeMass : Nat → ℝ) (R j : Nat) : ℝ :=
  ∑ d ∈ Finset.range R, degreeMass d * degreeMissProbability R j d

theorem degreeMissProbability_eq_gatewayMiss (R j d : Nat) :
    degreeMissProbability R j d = hypergeometricGatewayMiss R j d :=
  rfl

theorem degreeMissProbability_eq_zero_of_highDegree
    (R j d : Nat) (hjR : j ≤ R) (hhigh : R - j < d) :
    degreeMissProbability R j d = 0 := by
  rw [degreeMissProbability_eq_gatewayMiss]
  apply hypergeometricGatewayMiss_eq_zero_of_highDegree R j d hjR
  omega

/-- Exact support cutoff: degrees too large to avoid all `j` targets make no
contribution to the miss profile. -/
theorem coverageMissProfile_eq_filter
    (degreeMass : Nat → ℝ) (R j : Nat) (hjR : j ≤ R) :
    coverageMissProfile degreeMass R j =
      ∑ d ∈ (Finset.range R).filter (fun d => d ≤ R - j),
        degreeMass d * degreeMissProbability R j d := by
  rw [coverageMissProfile]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro d hdRange hdNotFilter
  have hhigh : R - j < d := by
    by_contra hnot
    exact hdNotFilter (by simp only [Finset.mem_filter, hdRange, true_and,
      Nat.le_of_not_gt hnot])
  rw [degreeMissProbability_eq_zero_of_highDegree R j d hjR hhigh, mul_zero]

/-- The campaign's capped-Zipf profile is exactly the previously verified
gateway-miss expectation, with the number of targets set to `j`. -/
theorem powerLawCoverageMissProfile_eq
    (a : ℝ) (R j : Nat) :
    coverageMissProfile (cappedZipfDegreeMass a R) R j =
      powerLawMoleculeGatewayMiss a R j := by
  rfl

end PowerLawSmallRAF
