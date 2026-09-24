import proofs.DUnstableCores.ClassicalMassAction.Rate
import proofs.DUnstableCores.CubicCoefficientsDim3

/-!
# Universal stability of the unpadded source

The positive steady-flux cone of the original literal source is one ray.  Its
classical Jacobians therefore form the positive right-scaling family of one
matrix.  An exact cubic Routh--Hurwitz calculation proves that entire family
strictly Hurwitz stable.
-/

namespace DUnstableCores

open Polynomial

/-- Strict cubic Routh--Hurwitz: positive coefficients and a strictly positive
second determinant force every characteristic root into the open left half
plane.  This leaf-local formulation avoids perturbing the shared cubic
infrastructure used by the already verified counterexample. -/
theorem hurwitzStable_of_cubic_coeff_pos_delta_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (a₁ a₂ a₃ : ℝ)
    (hpoly : IsCubicCharpoly A a₁ a₂ a₃)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (ha₃ : 0 < a₃)
    (hdelta : 0 < a₁ * a₂ - a₃) :
    HurwitzStable A := by
  have hnonpositive : HurwitzNonpositive A :=
    hurwitzNonpositive_of_cubic_coeff_nonneg_delta_nonneg
      A a₁ a₂ a₃ hpoly ha₁.le ha₂.le ha₃.le hdelta.le
  intro lam v heig
  have hle : lam.re ≤ 0 := by
    by_contra hnot
    exact hnonpositive ⟨lam, v, lt_of_not_ge hnot, heig⟩
  have hne : lam.re ≠ 0 := by
    intro hreZero
    have hroot := heig.isRoot_charpoly
    have hmap : (complexify A).charpoly =
        A.charpoly.map (algebraMap ℝ ℂ) := by
      simpa [complexify] using
        (Matrix.charpoly_map A (algebraMap ℝ ℂ))
    rw [hmap, hpoly] at hroot
    have hp := hroot.eq_zero
    have hre := congrArg Complex.re hp
    have him := congrArg Complex.im hp
    simp [pow_succ, Complex.mul_re, Complex.mul_im, hreZero] at hre him
    by_cases himZero : lam.im = 0
    · rw [himZero] at hre
      norm_num at hre
      linarith
    · have homega : lam.im ^ 2 = a₂ := by
        have hfactor : lam.im * (a₂ - lam.im ^ 2) = 0 := by
          nlinarith [him]
        have := (mul_eq_zero.mp hfactor).resolve_left himZero
        nlinarith
      nlinarith [hre]
  exact lt_of_le_of_ne hle hne

/-- The unpadded equilibrium-Jacobian template
`S * diag(2,3,2,2,2) * Y₀ᵀ`. -/
def classicalBaseJacobianTemplate : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2, 0, 0, 0;
     0, -48, -24, 24;
     8, -24, -44, 20;
     -4, 0, 16, -16]

/-- Lower-right cubic block after positive column scaling. -/
def classicalBaseCubicBlock (d : Fin 4 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-48 * d 1, -24 * d 2, 24 * d 3;
     -24 * d 1, -44 * d 2, 20 * d 3;
     0, 16 * d 2, -16 * d 3]

def classicalBaseCubicA1 (d : Fin 4 → ℝ) : ℝ :=
  48 * d 1 + 44 * d 2 + 16 * d 3

def classicalBaseCubicA2 (d : Fin 4 → ℝ) : ℝ :=
  1536 * d 1 * d 2 + 768 * d 1 * d 3 + 384 * d 2 * d 3

def classicalBaseCubicA3 (d : Fin 4 → ℝ) : ℝ :=
  18432 * d 1 * d 2 * d 3

theorem classicalBaseCubicBlock_charpoly (d : Fin 4 → ℝ) :
    IsCubicCharpoly (classicalBaseCubicBlock d)
      (classicalBaseCubicA1 d) (classicalBaseCubicA2 d)
      (classicalBaseCubicA3 d) := by
  have h1 : cubicCoeff1 (classicalBaseCubicBlock d) =
      classicalBaseCubicA1 d := by
    simp [cubicCoeff1, classicalBaseCubicBlock, classicalBaseCubicA1]
    ring
  have h2 : cubicCoeff2 (classicalBaseCubicBlock d) =
      classicalBaseCubicA2 d := by
    simp [cubicCoeff2, classicalBaseCubicBlock, classicalBaseCubicA2]
    ring
  have h3 : cubicCoeff3 (classicalBaseCubicBlock d) =
      classicalBaseCubicA3 d := by
    simp [cubicCoeff3, Matrix.det_fin_three, classicalBaseCubicBlock,
      classicalBaseCubicA3]
    ring
  rw [← h1, ← h2, ← h3]
  exact isCubicCharpoly_explicit (classicalBaseCubicBlock d)

theorem classicalBaseCubicBlock_hurwitzStable
    (d : Fin 4 → ℝ) (hd : ∀ i, 0 < d i) :
    HurwitzStable (classicalBaseCubicBlock d) := by
  have hd1 := hd 1
  have hd2 := hd 2
  have hd3 := hd 3
  apply hurwitzStable_of_cubic_coeff_pos_delta_pos
      (classicalBaseCubicBlock d)
      (classicalBaseCubicA1 d) (classicalBaseCubicA2 d)
      (classicalBaseCubicA3 d) (classicalBaseCubicBlock_charpoly d)
  · simp [classicalBaseCubicA1]
    linarith
  · simp [classicalBaseCubicA2]
    positivity
  · simp [classicalBaseCubicA3]
    positivity
  · rw [show classicalBaseCubicA1 d * classicalBaseCubicA2 d -
        classicalBaseCubicA3 d =
        73728 * d 1 ^ 2 * d 2 +
        36864 * d 1 ^ 2 * d 3 +
        67584 * d 1 * d 2 ^ 2 +
        58368 * d 1 * d 2 * d 3 +
        12288 * d 1 * d 3 ^ 2 +
        16896 * d 2 ^ 2 * d 3 +
        6144 * d 2 * d 3 ^ 2 by
      simp [classicalBaseCubicA1, classicalBaseCubicA2,
        classicalBaseCubicA3]
      ring]
    positivity

/-- Every positive right scaling of the unpadded template is strictly stable. -/
theorem classicalBaseJacobianTemplate_dStable :
    DStable classicalBaseJacobianTemplate := by
  intro d hd lam v heig
  by_cases hv0 : v 0 = 0
  · let w : Fin 3 → ℂ := fun i => v i.succ
    have hwne : w ≠ 0 := by
      intro hw
      apply heig.1
      funext i
      fin_cases i
      · exact hv0
      · exact congrFun hw 0
      · exact congrFun hw 1
      · exact congrFun hw 2
    have hwEig : HasEigenpair (classicalBaseCubicBlock d) lam w := by
      refine ⟨hwne, ?_⟩
      intro i
      fin_cases i
      · have h := heig.2 1
        simp [Matrix.mulVec, dotProduct, complexify, rightScale,
          classicalBaseJacobianTemplate, classicalBaseCubicBlock, w,
          Fin.sum_univ_succ, hv0] at h ⊢
        exact h
      · have h := heig.2 2
        simp [Matrix.mulVec, dotProduct, complexify, rightScale,
          classicalBaseJacobianTemplate, classicalBaseCubicBlock, w,
          Fin.sum_univ_succ, hv0] at h ⊢
        exact h
      · have h := heig.2 3
        simp [Matrix.mulVec, dotProduct, complexify, rightScale,
          classicalBaseJacobianTemplate, classicalBaseCubicBlock, w,
          Fin.sum_univ_succ, hv0] at h ⊢
        exact h
    exact classicalBaseCubicBlock_hurwitzStable d hd lam w hwEig
  · have hrow := heig.2 0
    simp [Matrix.mulVec, dotProduct, complexify, rightScale,
      classicalBaseJacobianTemplate, Fin.sum_univ_succ] at hrow
    have hlam : lam = (-2 * d 0 : ℝ) := by
      apply mul_right_cancel₀ hv0
      simpa [mul_assoc, mul_comm, mul_left_comm] using hrow.symm
    rw [hlam]
    norm_num
    linarith [hd 0]

/-- Any stationary classical flux on the unpadded source lies on the unique
positive ray `t * (2,3,2,2,2)`. -/
theorem classicalBase_stationary_flux_ray
    (M : ClassicalMassActionInstance classicalBaseCounterexampleSource)
    (hstat : ClassicalStationary M) :
    ∃ t : ℝ, 0 < t ∧
      ∀ r : Fin 5, classicalReactionFlux M r = t * (![2, 3, 2, 2, 2] r) := by
  let f : Fin 5 → ℝ := classicalReactionFlux M
  have hf : ∀ r, 0 < f r := by
    intro r
    exact mul_pos (M.rateConstant_pos r)
      (massActionMonomial_pos _ _ M.concentration_pos r)
  have h0 := hstat 0
  have h1 := hstat 1
  have h2 := hstat 2
  have h3 := hstat 3
  simp [SourceNetwork.stoich, classicalBaseCounterexampleSource,
    Fin.sum_univ_succ] at h0 h1 h2 h3
  change -f 0 + f 3 = 0 at h0
  change -(4 * f 1) + 6 * f 3 = 0 at h1
  change 4 * f 0 + (-(2 * f 1) + (-(4 * f 2) + (f 3 + 2 * f 4))) = 0 at h2
  change -(2 * f 0) + (2 * f 2 + (-(2 * f 3) + 2 * f 4)) = 0 at h3
  have hf3 : f 3 = f 0 := by
    linarith only [h0]
  rw [hf3] at h1 h2 h3
  have hf1 : f 1 = 3 * f 0 / 2 := by
    linarith only [h1]
  rw [hf1] at h2
  have hf2 : f 2 = f 0 := by
    linarith only [h2, h3]
  rw [hf2] at h3
  have hf4 : f 4 = f 0 := by
    linarith only [h3]
  refine ⟨f 0 / 2, div_pos (hf 0) (by norm_num), ?_⟩
  intro r
  fin_cases r <;> simp [f] <;> linarith

/-- At a positive stationary point, the literal-source Jacobian is one
positive right scaling of `classicalBaseJacobianTemplate`. -/
theorem classicalBase_stationary_jacobian_eq_rightScale
    (M : ClassicalMassActionInstance classicalBaseCounterexampleSource)
    (hstat : ClassicalStationary M) :
    ∃ d : Fin 4 → ℝ, (∀ i, 0 < d i) ∧
      classicalBaseCounterexampleSource.jacobian M.reactivity =
        rightScale classicalBaseJacobianTemplate d := by
  obtain ⟨t, ht, hflux⟩ := classicalBase_stationary_flux_ray M hstat
  let d : Fin 4 → ℝ := fun i => t / M.concentration i
  have hreact (r : Fin 5) (s : Fin 4) :
      M.reactivity.value r s =
        (classicalBaseCounterexampleSource.reactant s r : ℝ) *
          (t * (![2, 3, 2, 2, 2] r)) / M.concentration s := by
    rw [classical_reactivity_eq_reactant_mul_flux_div M, hflux r]
  refine ⟨d, fun i => div_pos ht (M.concentration_pos i), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SourceNetwork.jacobian, classicalBaseCounterexampleSource,
      SourceNetwork.stoich, classicalBaseJacobianTemplate, rightScale,
      d, Fin.sum_univ_succ, hreact] <;> ring

/-- **Universal unpadded stability theorem.**  Every positive stationary
classical mass-action instance on the original source is strictly Hurwitz
stable. -/
theorem classicalBase_every_positive_equilibrium_hurwitzStable
    (M : ClassicalMassActionInstance classicalBaseCounterexampleSource)
    (hstat : ClassicalStationary M) :
    HurwitzStable (classicalBaseCounterexampleSource.jacobian M.reactivity) := by
  obtain ⟨d, hd, hJ⟩ := classicalBase_stationary_jacobian_eq_rightScale M hstat
  rw [hJ]
  exact classicalBaseJacobianTemplate_dStable d hd

end DUnstableCores
