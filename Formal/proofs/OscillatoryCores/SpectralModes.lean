import proofs.OscillatoryCores.SpectralCrossing
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

namespace OscillatoryCores

open scoped BigOperators Matrix

theorem normalizedLinear_apply (t : ℝ) (u : State) :
    normalizedLinear t u = normalizedJacobian t *ᵥ u := by
  have hu : (∑ j : Fin 4, u j • (Pi.single j 1 : State)) = u := by
    ext i
    simp [Pi.single_apply]
  funext i
  calc
    normalizedLinear t u i = normalizedLinear t (∑ j : Fin 4, u j • (Pi.single j 1 : State)) i :=
      congrArg (fun v => normalizedLinear t v i) hu.symm
    _ = ∑ j : Fin 4, u j * normalizedLinear t (Pi.single j 1) i := by simp
    _ = (normalizedJacobian t *ᵥ u) i := by
      simp only [normalizedLinear_entry,Matrix.mulVec,dotProduct]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem imaginary_eigenvector_exists {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    ∃ q : Fin 4 → ℂ, q ≠ 0 ∧
      (normalizedJacobian t).map Complex.ofReal *ᵥ q =
        (Complex.I*(spectralFrequency t : ℂ)) • q := by
  obtain ⟨q,hq,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr (imaginary_jacobian_root ht hz)
  refine ⟨q,hq,?_⟩
  simpa only [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,sub_eq_zero,eq_comm] using hker

/-- Actual real center modes of the source derivative, obtained from its
singular complex characteristic matrix. -/
theorem real_center_modes {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    ∃ u v : State, u ≠ 0 ∧
      normalizedLinear t u = -(spectralFrequency t) • v ∧
      normalizedLinear t v = spectralFrequency t • u := by
  obtain ⟨q,hq,hAe⟩ := imaginary_eigenvector_exists ht hz
  let u : State := fun i => (q i).re
  let v : State := fun i => (q i).im
  have hu : normalizedLinear t u = -(spectralFrequency t) • v := by
    rw [normalizedLinear_apply]
    funext i
    have he := congrArg (fun w : Fin 4 → ℂ => (w i).re) hAe
    simpa [u,v,Matrix.mulVec,dotProduct,Complex.mul_re] using he
  have hv : normalizedLinear t v = spectralFrequency t • u := by
    rw [normalizedLinear_apply]
    funext i
    have he := congrArg (fun w : Fin 4 → ℂ => (w i).im) hAe
    simpa [u,v,Matrix.mulVec,dotProduct,Complex.mul_im] using he
  refine ⟨u,v,?_,hu,hv⟩
  intro hu0
  have hv0 : v = 0 := by
    rw [hu0,map_zero] at hu
    exact (smul_eq_zero.mp hu.symm).resolve_left (neg_ne_zero.mpr (ne_of_gt (spectralFrequency_pos ht)))
  apply hq
  funext i
  apply Complex.ext
  · exact congrFun hu0 i
  · exact congrFun hv0 i

end OscillatoryCores
