import proofs.ThreeSitePhosphorylation.CompanionSpectral

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

theorem companion_eigenvalue_root (r : ℝ) (z : ℂ) (y : Fin 9 → ℂ)
    (hy : y ≠ 0) (he : (companionSource r).mulVec y = z • y) :
    candidatePolynomial r z = 0 := by
  have h1 : y 1 = z^1*y 0 := by
    have hh := congrFun he (⟨0,by decide⟩ : Fin 9)
    have hk : y 1 = z*y 0 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    simpa using hk
  have h2 : y 2 = z^2*y 0 := by
    have hh := congrFun he (⟨1,by decide⟩ : Fin 9)
    have hk : y 2 = z*y 1 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h1]
    ring
  have h3 : y 3 = z^3*y 0 := by
    have hh := congrFun he (⟨2,by decide⟩ : Fin 9)
    have hk : y 3 = z*y 2 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h2]
    ring
  have h4 : y 4 = z^4*y 0 := by
    have hh := congrFun he (⟨3,by decide⟩ : Fin 9)
    have hk : y 4 = z*y 3 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h3]
    ring
  have h5 : y 5 = z^5*y 0 := by
    have hh := congrFun he (⟨4,by decide⟩ : Fin 9)
    have hk : y 5 = z*y 4 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h4]
    ring
  have h6 : y 6 = z^6*y 0 := by
    have hh := congrFun he (⟨5,by decide⟩ : Fin 9)
    have hk : y 6 = z*y 5 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h5]
    ring
  have h7 : y 7 = z^7*y 0 := by
    have hh := congrFun he (⟨6,by decide⟩ : Fin 9)
    have hk : y 7 = z*y 6 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h6]
    ring
  have h8 : y 8 = z^8*y 0 := by
    have hh := congrFun he (⟨7,by decide⟩ : Fin 9)
    have hk : y 8 = z*y 7 := by
      simpa [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] using hh
    rw [hk,h7]
    ring
  have hy0 : y 0 ≠ 0 := by
    intro hz
    apply hy
    ext i
    fin_cases i <;> simp [hz,h1,h2,h3,h4,h5,h6,h7,h8]
  have hlast := congrFun he (⟨8,by decide⟩ : Fin 9)
  simp [companionSource,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,h1,h2,h3,h4,h5,h6,h7,h8] at hlast
  have hp : candidatePolynomial r z*y 0 = 0 := by
    unfold candidatePolynomial
    push_cast
    linear_combination -hlast
  exact (mul_eq_zero.mp hp).resolve_right hy0

theorem source_eigenvalue_root (r : ℝ) (z : ℂ) (v : Fin 9 → ℂ)
    (hv : v ≠ 0) (he : (complexSource r).mulVec v = z • v) :
    candidatePolynomial r z = 0 := by
  let w := companionInverse.mulVec v
  have hinj : Function.Injective companionBasis.mulVec := by
    intro a b hab
    have hh := congrArg companionInverse.mulVec hab
    simpa only [Matrix.mulVec_mulVec,companion_inverse_complex,Matrix.one_mulVec] using hh
  have hwv : companionBasis.mulVec w = v := by
    dsimp [w]
    rw [Matrix.mulVec_mulVec,companion_inverse_complex_right,Matrix.one_mulVec]
  have hw : w ≠ 0 := by
    intro hz
    apply hv
    rw [hz,Matrix.mulVec_zero] at hwv
    exact hwv.symm
  apply companion_eigenvalue_root r z w hw
  apply hinj
  calc
    companionBasis.mulVec ((companionSource r).mulVec w) =
        (companionBasis*companionSource r).mulVec w := Matrix.mulVec_mulVec _ _ _
    _ = (complexSource r*companionBasis).mulVec w := by rw [source_companion_identity]
    _ = (complexSource r).mulVec (companionBasis.mulVec w) := (Matrix.mulVec_mulVec _ _ _).symm
    _ = z • companionBasis.mulVec w := by rw [hwv]; exact he
    _ = companionBasis.mulVec (z • w) := (Matrix.mulVec_smul _ _ _).symm

end
end ThreeSitePhosphorylation
