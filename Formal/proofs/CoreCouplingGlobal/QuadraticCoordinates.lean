import proofs.CoreCouplingGlobal.SpectralCoordinates

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- Exact nonlinear remainder of the physical mass-action field. -/
noncomputable def physicalQuadratic (e : ℝ) (x : ResponseVector) : ResponseVector :=
  ![-2*e*(x 0)^2+x 1*x 2,e*(x 0)^2-x 1*x 2,
    -x 1*x 2-4*(x 2)^2,2*(x 2)^2]

theorem responseVectorField_exact_quadratic (e : ℝ) (p x : ResponseVector) :
    responseVectorField e (p+x) = responseVectorField e p+
      (physicalJacobian e p).toLin' x+physicalQuadratic e x := by
  ext i
  fin_cases i <;>
    simp [responseVectorField,physicalJacobian,physicalQuadratic,fA,fB,fZ,fH,
      flagshipRates,dotProduct,Fin.sum_univ_succ] <;> ring

theorem stationary_vectorField_zero (e : ℝ) (s : State)
    (hss : Stationary (flagshipRates e) s) : responseVectorField e (encodeState s) = 0 := by
  ext i
  fin_cases i
  · exact hss.1
  · exact hss.2.1
  · exact hss.2.2.1
  · exact hss.2.2.2

theorem physicalQuadratic_smul (e a : ℝ) (x : ResponseVector) :
    physicalQuadratic e (a • x) = a^2 • physicalQuadratic e x := by
  ext i
  fin_cases i <;> simp [physicalQuadratic] <;> ring

/-- The middle dynamics in genuine eigenvector coordinates are diagonal plus an
exact quadratic polynomial, with no discarded Taylor terms. -/
theorem middle_exact_quadratic_coordinates (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (hz : s.z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
      (∀ i : Fin 3, μ i.castSucc < -(1/2:ℝ)) ∧ 0 < μ 3 ∧ μ 3 < 1/10 ∧
      ∀ x : ResponseVector,
        C.symm (responseVectorField e (encodeState s+C x)) =
          (fun i => μ i*x i)+C.symm (physicalQuadratic e (C x)) := by
  obtain ⟨μ,C,hstable,hu0,hu1,hC⟩ := middle_diagonal_coordinates e he hu s hs hss hz
  refine ⟨μ,C,hstable,hu0,hu1,?_⟩
  intro x
  rw [responseVectorField_exact_quadratic,stationary_vectorField_zero e s hss,
    zero_add,hC,map_add,C.symm_apply_apply]

end CoreCouplingGlobal
