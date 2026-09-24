import proofs.DUnstableCores.CubicCoefficientsDim3
import proofs.DUnstableCores.HopfCycleHolonomy

/-!
# Canonical three-cycle holonomy obstruction

The symmetric negative three-cycle is a genuine Hopf boundary but is not
D-unstable under any positive right-column scaling.  Its weak cubic
Routh--Hurwitz determinant is exactly the weighted sum-of-squares AM--GM
barrier.  This is the smallest higher-cycle obstruction found by the
theory-led numerical screen.
-/

namespace DUnstableCores

/-- The normalized negative three-cycle.  Its characteristic polynomial at
unit scaling is `(X+1)^3+8 = X^3+3X^2+3X+9`. -/
def symmetricNegativeThreeCycle : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1,  0, -8;
      1, -1,  0;
      0,  1, -1]

def symmetricNegativeThreeCycleReal : Fin 3 → ℝ := ![-2, 1, 1]

noncomputable def symmetricNegativeThreeCycleImag : Fin 3 → ℝ :=
  ![2 * Real.sqrt 3, Real.sqrt 3, 0]

/-- The obstruction is a literal positive-frequency imaginary-pair boundary,
not merely a coefficient artifact. -/
theorem symmetricNegativeThreeCycle_hasImaginaryPair :
    HasImaginaryPairWitness symmetricNegativeThreeCycle (Real.sqrt 3)
      symmetricNegativeThreeCycleReal symmetricNegativeThreeCycleImag := by
  have hsqrt : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨Real.sqrt_pos.2 (by norm_num), Or.inl ?_, ?_⟩
  · intro hzero
    have h0 : (-2 : ℝ) = 0 := by
      simpa [symmetricNegativeThreeCycleReal] using congrFun hzero 0
    norm_num at h0
  · intro i
    fin_cases i <;> constructor <;>
      simp [Matrix.mulVec, dotProduct, symmetricNegativeThreeCycle,
        symmetricNegativeThreeCycleReal, symmetricNegativeThreeCycleImag,
        Fin.sum_univ_three] <;>
      nlinarith [hsqrt]

private theorem three_variable_secant_barrier
    {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ (x + y + z) * (x * y + x * z + y * z) - 9 * x * y * z := by
  have h1 : 0 ≤ x * (y - z) ^ 2 := mul_nonneg hx (sq_nonneg _)
  have h2 : 0 ≤ y * (x - z) ^ 2 := mul_nonneg hy (sq_nonneg _)
  have h3 : 0 ≤ z * (x - y) ^ 2 := mul_nonneg hz (sq_nonneg _)
  nlinarith

/-- The exact universal cubic certificate.  The determinant term `9*d0*d1*d2`
is paid by the secant/AM--GM identity, with equality only on the symmetric
scaling ray. -/
theorem symmetricNegativeThreeCycle_cubicColumnCertificate :
    CubicColumnCertificate
      (fun i => symmetricNegativeThreeCycle i 0)
      (fun i => symmetricNegativeThreeCycle i 1)
      (fun i => symmetricNegativeThreeCycle i 2) := by
  intro d0 d1 d2 hd0 hd1 hd2
  dsimp only
  have hd0n : 0 ≤ d0 := hd0.le
  have hd1n : 0 ≤ d1 := hd1.le
  have hd2n : 0 ≤ d2 := hd2.le
  have hbarrier := three_variable_secant_barrier hd0n hd1n hd2n
  simp [cubicCoeff1, cubicCoeff2, cubicCoeff3, scaledColumns, fromColumns,
    symmetricNegativeThreeCycle, Matrix.det_fin_three]
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · positivity
  · nlinarith

/-- The canonical negative three-cycle never acquires an open-right-half-plane
root under positive right diagonal scaling.  Imaginary-axis equality is
allowed, exactly as required by `DNonUnstable`. -/
theorem symmetricNegativeThreeCycle_dNonUnstable :
    DNonUnstable symmetricNegativeThreeCycle := by
  have h := symmetricNegativeThreeCycle_cubicColumnCertificate.dNonUnstable
  have heq :
      fromColumns
        (fun i => symmetricNegativeThreeCycle i 0)
        (fun i => symmetricNegativeThreeCycle i 1)
        (fun i => symmetricNegativeThreeCycle i 2) =
        symmetricNegativeThreeCycle := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      rfl
  rw [← heq]
  exact h

/-- Consequently the canonical phase-carrying three-cycle is not itself a
D-unstable child. -/
theorem symmetricNegativeThreeCycle_not_dUnstable :
    ¬ DUnstable symmetricNegativeThreeCycle := by
  intro h
  have hnot : ¬ DNonUnstable symmetricNegativeThreeCycle :=
    (not_dNonUnstable_iff_dUnstable symmetricNegativeThreeCycle).mpr h
  exact hnot symmetricNegativeThreeCycle_dNonUnstable

end DUnstableCores
