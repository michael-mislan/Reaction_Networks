import Mathlib

/-!
Finite algebra for the revised inference section: the cancelled-determinant
form of the two-state switching target, and known-mixture calibration.
No stochastic statement, concentration inequality or interval-arithmetic
claim is asserted here; those are conventional proofs in the manuscript.
-/

namespace PhenotypeIdentification

variable {eS eT j00 j01 j10 j11 mu lam : ℝ}

/-- Off-diagonal entry of `M = L J Lᵀ` in terms of the uncancelled numerator
`N`, where `L` is the inverse of the two-state binary marker matrix. -/
theorem marker_offdiagonal (h : eT - eS ≠ 0) :
    ((eT / (eT - eS)) * j00 + (-(1 - eT) / (eT - eS)) * j10) * (-eS / (eT - eS))
      + ((eT / (eT - eS)) * j01 + (-(1 - eT) / (eT - eS)) * j11) * ((1 - eS) / (eT - eS))
    = (-eT * eS * j00 + eT * (1 - eS) * j01
        + (1 - eT) * eS * j10 - (1 - eT) * (1 - eS) * j11) / (eT - eS) ^ 2 := by
  field_simp
  ring

/-- The determinant of `M = L J Lᵀ` is the determinant of the observed block
divided by the squared marker contrast. -/
theorem marker_determinant (h : eT - eS ≠ 0) :
    (((eT / (eT - eS)) * j00 + (-(1 - eT) / (eT - eS)) * j10) * (eT / (eT - eS))
        + ((eT / (eT - eS)) * j01 + (-(1 - eT) / (eT - eS)) * j11) * (-(1 - eT) / (eT - eS)))
      * (((-eS / (eT - eS)) * j00 + ((1 - eS) / (eT - eS)) * j10) * (-eS / (eT - eS))
        + ((-eS / (eT - eS)) * j01 + ((1 - eS) / (eT - eS)) * j11) * ((1 - eS) / (eT - eS)))
    - (((eT / (eT - eS)) * j00 + (-(1 - eT) / (eT - eS)) * j10) * (-eS / (eT - eS))
        + ((eT / (eT - eS)) * j01 + (-(1 - eT) / (eT - eS)) * j11) * ((1 - eS) / (eT - eS)))
      * (((-eS / (eT - eS)) * j00 + ((1 - eS) / (eT - eS)) * j10) * (eT / (eT - eS))
        + ((-eS / (eT - eS)) * j01 + ((1 - eS) / (eT - eS)) * j11) * (-(1 - eT) / (eT - eS)))
    = (j00 * j11 - j01 * j10) / (eT - eS) ^ 2 := by
  field_simp
  ring

/-- The cancelled-determinant identity: every marker determinant factor cancels
before the target is evaluated.  `N` is the numerator above and `detJ` the
determinant of the observed deadline block. -/
theorem cancelled_target (N detJ : ℝ) (h : eT - eS ≠ 0) (hd : detJ ≠ 0) :
    lam * ((mu - eS) / (eT - eS)) * (N / (eT - eS) ^ 2) / (detJ / (eT - eS) ^ 2)
      = lam * (mu - eS) * N / ((eT - eS) * detJ) := by
  field_simp
  try ring

/-- Known-mixture calibration: two preparations with distinct known tolerant
fractions determine the binary channel exactly.  Pure states are `p₀ = 0`,
`p₁ = 1`. -/
theorem mixture_calibration (p0 p1 r0 r1 : ℝ) (hp : p1 - p0 ≠ 0)
    (h0 : r0 = eS + (eT - eS) * p0) (h1 : r1 = eS + (eT - eS) * p1) :
    eT - eS = (r1 - r0) / (p1 - p0)
      ∧ eS = (p1 * r0 - p0 * r1) / (p1 - p0)
      ∧ eT = ((1 - p0) * r1 - (1 - p1) * r0) / (p1 - p0) := by
  subst h0; subst h1
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- Bounded contamination: a nominal preparation whose true tolerant fraction is
within `η` of the ideal has marker mean within `η * |eT - eS|` of the ideal. -/
theorem contamination_bound (p eta : ℝ) (hp : |p| ≤ eta) :
    |(eS + (eT - eS) * p) - eS| ≤ eta * |eT - eS| := by
  have : (eS + (eT - eS) * p) - eS = (eT - eS) * p := by ring
  rw [this, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hp (abs_nonneg _)

/-- The five features of the direct switching target are determined by the
six-category coarsening: the fifth is the total initial-marker-one mass. -/
theorem six_category_features (p00 p01 p10 p11 p0D p1D : ℝ)
    (hsum : p00 + p01 + p10 + p11 + p0D + p1D = 1) :
    p10 + p11 + p1D = 1 - (p00 + p01 + p0D) := by
  linarith

end PhenotypeIdentification
