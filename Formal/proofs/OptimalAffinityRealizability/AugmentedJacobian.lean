import proofs.OptimalAffinityRealizability.NonlinearMassAction

namespace OptimalAffinityRealizability

open Matrix
noncomputable section

/-- The derivative matrix of the augmented log-stationarity map: the
controlled row is the coordinate constraint and every other row is `S E`. -/
def augmentedSteadyJacobian {n : ℕ} (source : SquareSource n)
    (E : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := fun i j =>
  if i = source.controlled then if j = source.controlled then 1 else 0
  else (source.netStoich * E) i j

theorem augmentedSteadyJacobian_mulVec_controlled {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ) :
    (augmentedSteadyJacobian source E).mulVec w source.controlled =
      w source.controlled := by
  simp [augmentedSteadyJacobian, Matrix.mulVec, dotProduct]

theorem augmentedSteadyJacobian_mulVec_noncontrolled {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → ℝ) (i : Fin n) (hi : i ≠ source.controlled) :
    (augmentedSteadyJacobian source E).mulVec w i =
      source.netStoich.mulVec (E.mulVec w) i := by
  calc
    (augmentedSteadyJacobian source E).mulVec w i =
        (source.netStoich * E).mulVec w i := by
          simp [augmentedSteadyJacobian, Matrix.mulVec, dotProduct, hi]
    _ = source.netStoich.mulVec (E.mulVec w) i := by
      rw [Matrix.mulVec_mulVec]

theorem augmentedSteadyJacobian_mulVec_injective {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source E) :
    Function.Injective (augmentedSteadyJacobian source E).mulVec := by
  intro x y hxy
  have hzero : (augmentedSteadyJacobian source E).mulVec (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  apply sub_eq_zero.mp
  apply hreduced (x - y)
  · have hc := congrFun hzero source.controlled
    rw [augmentedSteadyJacobian_mulVec_controlled] at hc
    exact hc
  · intro i hi
    have hrow := congrFun hzero i
    rw [augmentedSteadyJacobian_mulVec_noncontrolled source E (x - y) i hi] at hrow
    exact hrow

theorem augmentedSteadyJacobian_det_isUnit {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source E) :
    IsUnit (augmentedSteadyJacobian source E).det := by
  apply (augmentedSteadyJacobian source E).isUnit_iff_isUnit_det.mp
  exact Matrix.mulVec_injective_iff_isUnit.mp
    (augmentedSteadyJacobian_mulVec_injective source E hreduced)

def matrixContinuousLinearMap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

@[simp]
theorem matrixContinuousLinearMap_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    matrixContinuousLinearMap A w = A.mulVec w := rfl

/-- The algebraically certified augmented matrix as the continuous linear
equivalence required by the strict inverse-function theorem. -/
def augmentedSteadyContinuousLinearEquiv {n : ℕ} (source : SquareSource n)
    (E : Matrix (Fin n) (Fin n) ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source E) :
    (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := by
  let L := matrixContinuousLinearMap (augmentedSteadyJacobian source E)
  have hinj : Function.Injective L :=
    augmentedSteadyJacobian_mulVec_injective source E hreduced
  exact ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr (LinearMap.surjective_of_injective hinj))

@[simp]
theorem augmentedSteadyContinuousLinearEquiv_apply {n : ℕ}
    (source : SquareSource n) (E : Matrix (Fin n) (Fin n) ℝ)
    (hreduced : NoncontrolledSteadyJacobianInjective source E)
    (w : Fin n → ℝ) :
    augmentedSteadyContinuousLinearEquiv source E hreduced w =
      (augmentedSteadyJacobian source E).mulVec w := by
  rfl

theorem reconstructedLogReactionCurrent_hasStrictFDerivAt_zero {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    HasStrictFDerivAt (reconstructedLogReactionCurrent source J g q)
      (matrixContinuousLinearMap (literalCurrentJacobian source J g q)) 0 := by
  rw [hasStrictFDerivAt_pi']
  intro i
  let LR : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.reactant.transpose)
  let LP : (Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (matrixContinuousLinearMap source.product.transpose)
  have hR : HasStrictFDerivAt
      (fun z : Fin n → ℝ => source.reactant.transpose.mulVec z i) LR 0 := by
    exact LR.hasStrictFDerivAt
  have hP : HasStrictFDerivAt
      (fun z : Fin n → ℝ => source.product.transpose.mulVec z i) LP 0 := by
    exact LP.hasStrictFDerivAt
  have hforward := ((Real.hasStrictDerivAt_exp
    (source.reactant.transpose.mulVec (0 : Fin n → ℝ) i)).comp_hasStrictFDerivAt
      0 hR).const_mul (reconstructedForwardFlow J g q i)
  have hreverse := ((Real.hasStrictDerivAt_exp
    (source.product.transpose.mulVec (0 : Fin n → ℝ) i)).comp_hasStrictFDerivAt
      0 hP).const_mul (reconstructedReverseFlow J g q i)
  convert hforward.sub hreverse using 1
  ext w
  simp [LR, LP, literalCurrentJacobian, Matrix.sub_mulVec]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]

theorem reconstructedLogSourceDrift_hasStrictFDerivAt_zero {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    HasStrictFDerivAt (reconstructedLogSourceDrift source J g q)
      (matrixContinuousLinearMap
        (source.netStoich * literalCurrentJacobian source J g q)) 0 := by
  have hcurrent :=
    reconstructedLogReactionCurrent_hasStrictFDerivAt_zero source J g q
  have hcomp := (matrixContinuousLinearMap source.netStoich).hasStrictFDerivAt.comp
    0 hcurrent
  convert hcomp using 1
  ext w i
  exact congrFun (Matrix.mulVec_mulVec w source.netStoich
    (literalCurrentJacobian source J g q)).symm i

theorem augmentedLogStationarity_hasStrictFDerivAt_zero {n : ℕ}
    (source : SquareSource n) (J : ℝ) (g q : Fin n → ℝ) :
    HasStrictFDerivAt (augmentedLogStationarity source J g q)
      (matrixContinuousLinearMap
        (augmentedSteadyJacobian source (literalCurrentJacobian source J g q))) 0 := by
  rw [hasStrictFDerivAt_pi']
  intro i
  by_cases hi : i = source.controlled
  · subst i
    let coord : (Fin n → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj source.controlled
    convert coord.hasStrictFDerivAt using 1
    · apply funext
      intro x
      rw [augmentedLogStationarity, if_pos rfl]
      exact (ContinuousLinearMap.proj_apply source.controlled x).symm
    · ext w
      simpa [coord] using augmentedSteadyJacobian_mulVec_controlled source
        (literalCurrentJacobian source J g q) w
  · have hcomponent := (hasStrictFDerivAt_pi'.mp
      (reconstructedLogSourceDrift_hasStrictFDerivAt_zero source J g q)) i
    convert hcomponent using 1
    · simp [augmentedLogStationarity, hi]
    · ext w
      simpa using augmentedSteadyJacobian_mulVec_noncontrolled source
        (literalCurrentJacobian source J g q) w i hi

end
end OptimalAffinityRealizability
