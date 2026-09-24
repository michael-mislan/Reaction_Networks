import proofs.CoreCouplingGlobal.PhysicalUnstable

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology

theorem MiddlePerronCoordinates.linearBinding {e : ℝ} {s : State}
    {μ : Fin 4 → ℝ} {C : ResponseVector ≃L[ℝ] ResponseVector}
    (hC : MiddlePerronCoordinates e s μ C)
    (hss : Stationary (flagshipRates e) s) (x : ResponseVector) :
    (physicalJacobian e (encodeState s)).toLin' (C x)=C (fun i => μ i*x i) := by
  have h := hC.equation x
  rw [responseVectorField_exact_quadratic,stationary_vectorField_zero e s hss,
    zero_add,map_add] at h
  have hh := congrArg C (add_right_cancel h)
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh

/-- A growing physical eigenmode is visible in the B concentration. -/
theorem unstable_eigenvector_B_ne_zero (e : ℝ) (he : 0 ≤ e)
    (s : State) (hs : s.Positive) (lam : ℝ) (hlam : 0 < lam)
    (v : ResponseVector) (hv0 : v ≠ 0)
    (hv : (physicalJacobian e (encodeState s)).toLin' v=lam • v) : v 1 ≠ 0 := by
  intro hb
  have h0 := congrFun hv (0 : Fin 4)
  have h1 := congrFun hv (1 : Fin 4)
  have h2 := congrFun hv (2 : Fin 4)
  simp [physicalJacobian,encodeState,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hb] at h0 h1 h2
  have ha : v 0=0 := by
    have hsum : (lam+1+2*e*s.A)*v 0=0 := by linear_combination -h0-h1
    have hcoef : 0 < lam+1+2*e*s.A := by
      have hApos := hs.1
      positivity
    exact (mul_eq_zero.mp hsum).resolve_left hcoef.ne'
  have hz : v 2=0 := by
    rw [ha] at h1
    have hprod : s.B*v 2=0 := by linarith
    exact (mul_eq_zero.mp hprod).resolve_left hs.2.1.ne'
  have hH : v 3=0 := by rw [ha,hz] at h2; linarith
  apply hv0
  ext i
  fin_cases i
  · exact ha
  · exact hb
  · exact hz
  · exact hH

theorem unstable_physical_tangent_eigenvector (e : ℝ) (s : State)
    (hss : Stationary (flagshipRates e) s) (μ : Fin 4 → ℝ)
    (C : ResponseVector ≃L[ℝ] ResponseVector) (hC : MiddlePerronCoordinates e s μ C) :
    C (unstableInclusion 1) ≠ 0 ∧
      (physicalJacobian e (encodeState s)).toLin' (C (unstableInclusion 1))=
        μ 3 • C (unstableInclusion 1) := by
  constructor
  · intro h
    have hh := C.injective (h.trans C.map_zero.symm)
    have hlast := congrFun hh (3 : Fin 4)
    simp [unstableInclusion] at hlast
  · rw [hC.linearBinding hss]
    have hdiag : (fun i => μ i*unstableInclusion 1 i)=μ 3 • unstableInclusion 1 := by
      ext i
      by_cases hi : i=3
      · simp [hi,unstableInclusion]
      · simp [hi,unstableInclusion]
    rw [hdiag,C.map_smul]

theorem unstable_physical_tangent_B_ne_zero (e : ℝ) (he : 0 ≤ e)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s)
    (μ : Fin 4 → ℝ) (C : ResponseVector ≃L[ℝ] ResponseVector)
    (hC : MiddlePerronCoordinates e s μ C) : C (unstableInclusion 1) 1 ≠ 0 := by
  obtain ⟨hne,heigen⟩ := unstable_physical_tangent_eigenvector e s hss μ C hC
  exact unstable_eigenvector_B_ne_zero e he s hs (μ 3) hC.unstable _ hne heigen

end CoreCouplingGlobal
