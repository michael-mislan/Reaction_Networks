import proofs.CoreCouplingGlobal.PerronTrajectories

namespace CoreCouplingGlobal

noncomputable def physicalBilinear (e : ℝ) :
    ResponseVector →L[ℝ] ResponseVector →L[ℝ] ResponseVector :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => LinearMap.toContinuousLinearMap
        { toFun := fun y =>
            ![-2*e*x 0*y 0+x 1*y 2,e*x 0*y 0-x 1*y 2,
              -x 1*y 2-4*x 2*y 2,2*x 2*y 2]
          map_add' := by
            intro y z
            ext i
            fin_cases i <;> simp <;> ring
          map_smul' := by
            intro a y
            ext i
            fin_cases i <;> simp <;> ring }
      map_add' := by
        intro x y
        ext z i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro a x
        ext y i
        fin_cases i <;> simp <;> ring }

theorem physicalBilinear_diagonal (e : ℝ) (x : ResponseVector) :
    physicalBilinear e x x=physicalQuadratic e x := by
  ext i
  fin_cases i <;> simp [physicalBilinear,physicalQuadratic] <;> ring

noncomputable def bilinearCoefficients
    (B : ResponseVector →L[ℝ] ResponseVector →L[ℝ] ResponseVector)
    (i j k : Fin 4) : ℝ := B (Pi.single j 1) (Pi.single k 1) i

theorem coefficientQuadratic_bilinear
    (B : ResponseVector →L[ℝ] ResponseVector →L[ℝ] ResponseVector)
    (x : ResponseVector) :
    coefficientQuadratic (bilinearCoefficients B) x=B x x := by
  have hx : x=∑ j : Fin 4, x j • (Pi.single j 1 : ResponseVector) := by
    ext i
    simp [Finset.sum_apply,Pi.single_apply]
  have hsum : B x x=∑ j : Fin 4, ∑ k : Fin 4,
      (x j*x k) • B (Pi.single j 1) (Pi.single k 1) := by
    conv_lhs => rw [hx]
    simp only [map_sum,map_smul,ContinuousLinearMap.sum_apply,
      ContinuousLinearMap.smul_apply,Finset.smul_sum,smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _hj
    apply Finset.sum_congr rfl
    intro k _hk
    rw [mul_comm]
  rw [hsum]
  ext i
  simp only [coefficientQuadratic,bilinearCoefficients,Finset.sum_apply,
    Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro k _hk
  ring

/-- The coefficients used by the trajectory construction represent the actual
physical quadratic nonlinearity after any continuous linear coordinate change. -/
theorem physical_quadratic_has_coefficients (e : ℝ)
    (C : ResponseVector ≃L[ℝ] ResponseVector) :
    ∃ q : Fin 4 → Fin 4 → Fin 4 → ℝ,
      ∀ x : ResponseVector, coefficientQuadratic q x=C.symm (physicalQuadratic e (C x)) := by
  let B := (physicalBilinear e).bilinearComp C.toContinuousLinearMap C.toContinuousLinearMap
  let CB : ResponseVector →L[ℝ] ResponseVector →L[ℝ] ResponseVector :=
    (ContinuousLinearMap.compL ℝ ResponseVector ResponseVector ResponseVector
      C.symm.toContinuousLinearMap).comp B
  refine ⟨bilinearCoefficients CB,?_⟩
  intro x
  rw [coefficientQuadratic_bilinear]
  change C.symm (physicalBilinear e (C x) (C x))=C.symm (physicalQuadratic e (C x))
  rw [physicalBilinear_diagonal]

end CoreCouplingGlobal
