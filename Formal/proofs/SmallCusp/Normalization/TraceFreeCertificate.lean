import proofs.SmallCusp.Normalization.FluxJet

/-!
# Trace-free normalized cusp jets

This is the exact necessary interface consumed by the finite negative
classification.  It omits Jacobian trace and the normalization gauges
`p·q = 1`, `p·h = 0`, because neither is preserved by state-coordinate
scaling.  All geometric zero/nonzero cusp conditions are retained.
-/

namespace SmallCusp

def TraceFreeNormalizedValid {m : ℕ} {Q : SmallPlanarNetwork m}
    (C : CuspCertificate Q) : Prop :=
  C.state = unitState ∧
  PositiveVector C.rates ∧
  (∀ i, Q.massAction C.rates C.state i = 0) ∧
  (∀ i, Q.jacobianApply C.rates C.state C.rightKernel i = 0) ∧
  (∀ j, ∑ i : Species, C.leftKernel i * Q.jacobian C.rates C.state i j = 0) ∧
  C.rightKernel ≠ 0 ∧
  C.leftKernel ≠ 0 ∧
  dot C.leftKernel
      (Q.hessianApply C.rates C.state C.rightKernel C.rightKernel) = 0 ∧
  (∀ i, Q.jacobianApply C.rates C.state C.centerCorrection i =
      -Q.hessianApply C.rates C.state C.rightKernel C.rightKernel i) ∧
  dot C.leftKernel
      (Q.hessianApply C.rates C.state C.rightKernel C.centerCorrection) ≠ 0 ∧
  Matrix.det C.unfoldingMatrix ≠ 0

noncomputable def normalizedTraceFreeCertificate {m : ℕ} {Q : SmallPlanarNetwork m}
    (C : CuspCertificate Q) : CuspCertificate Q where
  state := unitState
  rates := equilibriumFlux Q C.rates C.state
  rightKernel := scaleVectorByState C.state C.rightKernel
  leftKernel := C.leftKernel
  centerCorrection := scaleVectorByState C.state C.centerCorrection
  unfoldingDirections := fun col =>
    scaleRateDirection Q C.state (C.unfoldingDirections col)

private theorem equilibriumFlux_positive {m : ℕ} (Q : SmallPlanarNetwork m)
    (k : Fin m → ℝ) (x : Species → ℝ)
    (hk : PositiveVector k) (hx : PositiveVector x) :
    PositiveVector (equilibriumFlux Q k x) := by
  intro r
  apply mul_pos (hk r)
  apply Finset.prod_pos
  intro i _
  exact pow_pos (hx i) _

private theorem scaledVector_ne_zero (x v : Species → ℝ)
    (hx : PositiveVector x) (hv : v ≠ 0) :
    scaleVectorByState x v ≠ 0 := by
  intro hscaled
  apply hv
  funext i
  have hi := congrFun hscaled i
  simp only [scaleVectorByState, Pi.zero_apply] at hi
  exact (div_eq_zero_iff).mp hi |>.resolve_right (ne_of_gt (hx i))

theorem normalizedTraceFreeCertificate_valid {m : ℕ}
    {Q : SmallPlanarNetwork m} (C : CuspCertificate Q) (hC : C.Valid) :
    TraceFreeNormalizedValid (normalizedTraceFreeCertificate C) := by
  rcases hC with ⟨hx, hk, heq, hright, hleft, hnorm, _htrace,
    hfold, hcenter, _hgauge, hcubic, hunfold⟩
  let D := normalizedTraceFreeCertificate C
  have hq : C.rightKernel ≠ 0 := by
    intro hzero
    have : dot C.leftKernel C.rightKernel = 0 := by simp [hzero, dot]
    linarith
  have hp : C.leftKernel ≠ 0 := by
    intro hzero
    have : dot C.leftKernel C.rightKernel = 0 := by simp [hzero, dot]
    linarith
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact equilibriumFlux_positive Q C.rates C.state hk hx
  · intro i
    change Q.massAction (equilibriumFlux Q C.rates C.state) unitState i = 0
    rw [massAction_equilibriumFlux]
    exact heq i
  · intro i
    change Q.jacobianApply (equilibriumFlux Q C.rates C.state) unitState
      (scaleVectorByState C.state C.rightKernel) i = 0
    rw [jacobianApply_equilibriumFlux Q C.rates C.state C.rightKernel hx]
    exact hright i
  · intro j
    change ∑ i : Species, C.leftKernel i *
      Q.jacobian (equilibriumFlux Q C.rates C.state) unitState i j = 0
    simp_rw [jacobian_equilibriumFlux Q C.rates C.state hx]
    calc
      (∑ i : Species, C.leftKernel i *
          (Q.jacobian C.rates C.state i j * C.state j)) =
          (∑ i : Species, C.leftKernel i *
            Q.jacobian C.rates C.state i j) * C.state j := by
        simp_rw [← mul_assoc]
        rw [Finset.sum_mul]
      _ = 0 := by rw [hleft j, zero_mul]
  · exact scaledVector_ne_zero C.state C.rightKernel hx hq
  · exact hp
  · change dot C.leftKernel
      (Q.hessianApply (equilibriumFlux Q C.rates C.state) unitState
        (scaleVectorByState C.state C.rightKernel)
        (scaleVectorByState C.state C.rightKernel)) = 0
    have hh := funext fun i => hessianApply_equilibriumFlux Q C.rates C.state
      C.rightKernel C.rightKernel hx i
    rw [hh]
    exact hfold
  · intro i
    change Q.jacobianApply (equilibriumFlux Q C.rates C.state) unitState
        (scaleVectorByState C.state C.centerCorrection) i =
      -Q.hessianApply (equilibriumFlux Q C.rates C.state) unitState
        (scaleVectorByState C.state C.rightKernel)
        (scaleVectorByState C.state C.rightKernel) i
    rw [jacobianApply_equilibriumFlux Q C.rates C.state C.centerCorrection hx]
    rw [hessianApply_equilibriumFlux Q C.rates C.state
      C.rightKernel C.rightKernel hx]
    exact hcenter i
  · change dot C.leftKernel
      (Q.hessianApply (equilibriumFlux Q C.rates C.state) unitState
        (scaleVectorByState C.state C.rightKernel)
        (scaleVectorByState C.state C.centerCorrection)) ≠ 0
    have hh := funext fun i => hessianApply_equilibriumFlux Q C.rates C.state
      C.rightKernel C.centerCorrection hx i
    rw [hh]
    exact hcubic
  · have hMatrix : D.unfoldingMatrix = C.unfoldingMatrix := by
      ext row col
      by_cases hr : row = 0
      · simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, hr, if_pos, D,
          normalizedTraceFreeCertificate]
        have hv := funext fun i => rateFieldVariation_scaled Q C.state
          (C.unfoldingDirections col) i
        rw [hv]
      · simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, hr, if_false, D,
          normalizedTraceFreeCertificate]
        have hv := funext fun i => rateJacobianVariation_scaled Q C.state
          C.rightKernel hx (C.unfoldingDirections col) i
        rw [hv]
    rw [hMatrix]
    exact hunfold

theorem admitsTransverseCusp_implies_traceFreeNormalized {m : ℕ}
    (Q : SmallPlanarNetwork m) :
    AdmitsTransverseCusp Q →
      ∃ D : CuspCertificate Q, TraceFreeNormalizedValid D := by
  rintro ⟨C, hC⟩
  exact ⟨normalizedTraceFreeCertificate C,
    normalizedTraceFreeCertificate_valid C hC⟩

/-- State normalization multiplies each Jacobian column by a positive state
coordinate.  Hence the nonzero trace in a cusp certificate supplies a nonzero
entry in its normalized Jacobian without any finite source check. -/
theorem normalizedTraceFreeCertificate_jacobian_nonzero {m : ℕ}
    {Q : SmallPlanarNetwork m} (C : CuspCertificate Q) (hC : C.Valid) :
    Q.jacobian (normalizedTraceFreeCertificate C).rates unitState 0 0 ≠ 0 ∨
    Q.jacobian (normalizedTraceFreeCertificate C).rates unitState 0 1 ≠ 0 ∨
    Q.jacobian (normalizedTraceFreeCertificate C).rates unitState 1 0 ≠ 0 ∨
    Q.jacobian (normalizedTraceFreeCertificate C).rates unitState 1 1 ≠ 0 := by
  rcases hC with ⟨hx, _hk, _heq, _hright, _hleft, _hnorm, htrace, _⟩
  by_contra hzero
  simp only [not_or, not_not] at hzero
  have h00 := jacobian_equilibriumFlux Q C.rates C.state hx 0 0
  have h11 := jacobian_equilibriumFlux Q C.rates C.state hx 1 1
  change Q.jacobian (equilibriumFlux Q C.rates C.state) unitState 0 0 =
      Q.jacobian C.rates C.state 0 0 * C.state 0 at h00
  change Q.jacobian (equilibriumFlux Q C.rates C.state) unitState 1 1 =
      Q.jacobian C.rates C.state 1 1 * C.state 1 at h11
  have hj00 : Q.jacobian C.rates C.state 0 0 = 0 := by
    apply (mul_eq_zero.mp (h00.symm.trans hzero.1)).resolve_right
    exact ne_of_gt (hx 0)
  have hj11 : Q.jacobian C.rates C.state 1 1 = 0 := by
    apply (mul_eq_zero.mp (h11.symm.trans hzero.2.2.2)).resolve_right
    exact ne_of_gt (hx 1)
  exact htrace (by rw [hj00, hj11, zero_add])

end SmallCusp
