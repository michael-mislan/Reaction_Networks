import proofs.PowerLawSmallRAF.CoverageInclusionExclusion

namespace PowerLawSmallRAF

theorem degreeMissProbability_eq_symmetricChoose
    (R j d : Nat) (hjR : j ≤ R) (hdR : d ≤ R) :
    degreeMissProbability R j d =
      (Nat.choose (R - d) j : ℝ) / Nat.choose R j := by
  by_cases hlow : d + j ≤ R
  · rw [degreeMissProbability_eq_gatewayMiss]
    exact hypergeometricGatewayMiss_eq_symmetricChoose R j d hlow
  · have hdhigh : R - j < d := by omega
    have hjhigh : R - d < j := by omega
    rw [degreeMissProbability, Nat.choose_eq_zero_of_lt hdhigh,
      Nat.choose_eq_zero_of_lt hjhigh]
    simp

/-- Falling-factorial form of the one-degree miss probability. -/
theorem degreeMissProbability_eq_descFactorialRatio
    (R j d : Nat) (hjR : j ≤ R) (hdR : d ≤ R) :
    degreeMissProbability R j d =
      (Nat.descFactorial (R - d) j : ℝ) /
        Nat.descFactorial R j := by
  rw [degreeMissProbability_eq_symmetricChoose R j d hjR hdR,
    Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  push_cast
  have hfac : (j.factorial : ℝ) ≠ 0 := by
    exact_mod_cast j.factorial_ne_zero
  field_simp

/-- Exact finite factorial-moment expansion of the miss profile. -/
theorem coverageMissProfile_eq_descFactorialMoment
    (degreeMass : Nat → ℝ) (R j : Nat) (hjR : j ≤ R) :
    coverageMissProfile degreeMass R j =
      ∑ d ∈ Finset.range R, degreeMass d *
        ((Nat.descFactorial (R - d) j : ℝ) /
          Nat.descFactorial R j) := by
  rw [coverageMissProfile]
  apply Finset.sum_congr rfl
  intro d hd
  rw [degreeMissProbability_eq_descFactorialRatio R j d hjR
    (Nat.le_of_lt (Finset.mem_range.mp hd))]

/-- Two-sided moment envelope for the capped-Zipf miss profile.  The lower
bound uses the first moment; the upper correction also retains the second
moment. -/
theorem powerLawCoverageMissProfile_bounds
    (a : ℝ) (R j : Nat) (ha : 1 < a) (hR : 2 ≤ R)
    (hj0 : 0 < j) (hjR : j ≤ R) :
    1 - (j : ℝ) * windowZipfMean a R /
          ((R - j + 1 : Nat) : ℝ) ≤
        coverageMissProfile (cappedZipfDegreeMass a R) R j ∧
      coverageMissProfile (cappedZipfDegreeMass a R) R j ≤
        1 - ((j : ℝ) * windowZipfMean a R / (R : ℝ) -
          ((j : ℝ) / ((R - j + 1 : Nat) : ℝ)) ^ 2 *
            windowZipfSecondMoment a R) := by
  have hhit := powerLawMoleculeGatewayHit_bounds a R j ha hR hj0 hjR
  rw [powerLawCoverageMissProfile_eq]
  change 1 - (j : ℝ) * windowZipfMean a R /
        ((R - j + 1 : Nat) : ℝ) ≤ powerLawMoleculeGatewayMiss a R j ∧
    powerLawMoleculeGatewayMiss a R j ≤
      1 - ((j : ℝ) * windowZipfMean a R / (R : ℝ) -
        ((j : ℝ) / ((R - j + 1 : Nat) : ℝ)) ^ 2 *
          windowZipfSecondMoment a R)
  dsimp [powerLawMoleculeGatewayHit] at hhit
  constructor <;> linarith

end PowerLawSmallRAF
