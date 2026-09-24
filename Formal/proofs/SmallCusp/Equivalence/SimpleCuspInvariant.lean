import proofs.SmallCusp.Equivalence.SimpleTransport

/-! A transverse cusp is invariant under positive reaction-column scaling. -/

namespace SmallCusp

theorem simplyEquivalent_symm {m : ℕ} {Q P : SmallPlanarNetwork m} :
    SimplyEquivalent Q P → SimplyEquivalent P Q := by
  rintro ⟨e, c, hc, hReact, hStoich⟩
  let d : Fin m → ℝ := fun s => 1 / c (e.symm s)
  refine ⟨e.symm, d, ?_, ?_, ?_⟩
  · intro s
    exact one_div_pos.mpr (hc (e.symm s))
  · intro s
    simpa using (hReact (e.symm s)).symm
  · intro i s
    have hs := hStoich i (e.symm s)
    simp only [Equiv.apply_symm_apply] at hs
    dsimp [d]
    field_simp [ne_of_gt (hc (e.symm s))] at hs ⊢
    nlinarith

theorem simplyEquivalent_admitsTransverseCusp_forward {m : ℕ}
    {Q P : SmallPlanarNetwork m} (hQP : SimplyEquivalent Q P) :
    AdmitsTransverseCusp Q → AdmitsTransverseCusp P := by
  rcases hQP with ⟨e, c, hc, hReact, hStoich⟩
  rintro ⟨C, hC⟩
  let D : CuspCertificate P := {
    state := C.state
    rates := simpleRateTransport e c C.rates
    rightKernel := C.rightKernel
    leftKernel := C.leftKernel
    centerCorrection := C.centerCorrection
    unfoldingDirections := fun a =>
      simpleRateTransport e c (C.unfoldingDirections a)
  }
  refine ⟨D, ?_⟩
  rcases hC with
    ⟨hx, hk, heq, hright, hleft, hnorm, htrace, hquad,
      hcenter, hcenterNorm, hcubic, hunfold⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [D] using hx
  · simpa [D] using simpleRateTransport_positive e hc hk
  · intro i
    change P.massAction (simpleRateTransport e c C.rates) C.state i = 0
    rw [simple_massAction_transport e c hc hReact hStoich]
    exact heq i
  · intro i
    change P.jacobianApply (simpleRateTransport e c C.rates)
      C.state C.rightKernel i = 0
    rw [simple_jacobianApply_transport e c hc hReact hStoich]
    exact hright i
  · intro j
    change (∑ i : Species, C.leftKernel i *
      P.jacobian (simpleRateTransport e c C.rates) C.state i j) = 0
    calc
      _ = ∑ i : Species, C.leftKernel i * Q.jacobian C.rates C.state i j := by
        apply Finset.sum_congr rfl
        intro i _
        rw [simple_jacobian_transport e c hc hReact hStoich]
      _ = 0 := hleft j
  · simpa [D] using hnorm
  · change P.jacobian (simpleRateTransport e c C.rates) C.state 0 0 +
      P.jacobian (simpleRateTransport e c C.rates) C.state 1 1 ≠ 0
    rw [simple_jacobian_transport e c hc hReact hStoich,
      simple_jacobian_transport e c hc hReact hStoich]
    exact htrace
  · change dot C.leftKernel
      (P.hessianApply (simpleRateTransport e c C.rates)
        C.state C.rightKernel C.rightKernel) = 0
    have hh : P.hessianApply (simpleRateTransport e c C.rates)
        C.state C.rightKernel C.rightKernel =
      Q.hessianApply C.rates C.state C.rightKernel C.rightKernel := by
      funext i
      exact simple_hessianApply_transport e c hc hReact hStoich
        C.rates C.state C.rightKernel C.rightKernel i
    rw [hh]
    exact hquad
  · intro i
    change P.jacobianApply (simpleRateTransport e c C.rates)
        C.state C.centerCorrection i =
      -P.hessianApply (simpleRateTransport e c C.rates)
        C.state C.rightKernel C.rightKernel i
    rw [simple_jacobianApply_transport e c hc hReact hStoich,
      simple_hessianApply_transport e c hc hReact hStoich]
    exact hcenter i
  · simpa [D] using hcenterNorm
  · change dot C.leftKernel
      (P.hessianApply (simpleRateTransport e c C.rates)
        C.state C.rightKernel C.centerCorrection) ≠ 0
    have hh : P.hessianApply (simpleRateTransport e c C.rates)
        C.state C.rightKernel C.centerCorrection =
      Q.hessianApply C.rates C.state C.rightKernel C.centerCorrection := by
      funext i
      exact simple_hessianApply_transport e c hc hReact hStoich
        C.rates C.state C.rightKernel C.centerCorrection i
    rw [hh]
    exact hcubic
  · have hMatrix : D.unfoldingMatrix = C.unfoldingMatrix := by
      ext row col
      by_cases hr : row = 0
      · simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, hr, if_pos, D]
        exact simple_dot_rateFieldVariation_transport e c hc hReact hStoich
          C.leftKernel C.state (C.unfoldingDirections col)
      · simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, hr, D]
        exact simple_dot_rateJacobianVariation_transport e c hc hReact hStoich
          C.leftKernel C.state C.rightKernel (C.unfoldingDirections col)
    rw [hMatrix]
    exact hunfold

theorem simplyEquivalent_admitsTransverseCusp_iff {m : ℕ}
    {Q P : SmallPlanarNetwork m} (hQP : SimplyEquivalent Q P) :
    AdmitsTransverseCusp Q ↔ AdmitsTransverseCusp P := by
  constructor
  · exact simplyEquivalent_admitsTransverseCusp_forward hQP
  · exact simplyEquivalent_admitsTransverseCusp_forward (simplyEquivalent_symm hQP)

end SmallCusp
