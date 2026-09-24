import proofs.OscillatoryCores.EigenvalueBranch

namespace OscillatoryCores

open Filter
open scoped Topology ContDiff Matrix

theorem crossing_roots_classified {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) {z : ℂ} (hroot : quarticC t z=0) :
    z=Complex.I*(spectralFrequency t : ℂ) ∨
      z=-(Complex.I*(spectralFrequency t : ℂ)) ∨ z.re < 0 := by
  rw [complex_crossing_factorization ht hz] at hroot
  rcases mul_eq_zero.mp hroot with h | h
  · have hw : (spectralFrequency t : ℂ)^2 = (a3 t : ℂ)/(a1 t : ℂ) := by
      exact_mod_cast spectralFrequency_sq ht
    have he : z^2 = (Complex.I*(spectralFrequency t : ℂ))^2 := by
      rw [mul_pow,Complex.I_sq,hw]
      linear_combination h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · right; right
    have hp := coefficients_pos ht
    apply positive_quadratic_roots_left hp.1
      (div_pos (mul_pos hp.1 hp.2.2.2) hp.2.2.1)
    exact_mod_cast h

/-- Full literal spectral certificate: the unique positive crossing has a
simple imaginary root, all other roots lie strictly left except its conjugate,
and an actual smooth characteristic-root branch crosses with positive speed. -/
theorem source_spectral_crossing :
    ∃ t w : ℝ, 1/2 < t ∧ t < 1 ∧ 0 < w ∧
      crossingPolynomial t=0 ∧
      ((Complex.I*(w : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
        (normalizedJacobian t).map Complex.ofReal).det=0 ∧
      quarticDerivativeC t (Complex.I*(w : ℂ)) ≠ 0 ∧
      (∀ z : ℂ, (z • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
        (normalizedJacobian t).map Complex.ofReal).det=0 →
        z=Complex.I*(w : ℂ) ∨ z=-(Complex.I*(w : ℂ)) ∨ z.re < 0) ∧
      ∃ eig : ℝ → ℂ, ∃ d : ℂ, eig t=Complex.I*(w : ℂ) ∧
        ContDiffAt ℝ ∞ eig t ∧ HasDerivAt eig d t ∧ 0 < d.re ∧
        (∀ᶠ s in 𝓝 t, ((eig s) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
          (normalizedJacobian s).map Complex.ofReal).det=0) := by
  obtain ⟨t,htlo,hthi,hz⟩ := crossing_exists
  have ht : 0 < t := by linarith
  obtain ⟨ψ,hψ0,hψsmooth,hψroot,hψd⟩ := eigenvalue_branch_exists ht hz
  refine ⟨t,spectralFrequency t,htlo,hthi,spectralFrequency_pos ht,hz,
    imaginary_jacobian_root ht hz,imaginary_root_simple ht,?_,?_
    ⟩
  · intro z h
    rw [complex_characteristic_determinant] at h
    exact crossing_roots_classified ht hz h
  · refine ⟨fun s => ψ (s : ℂ),_,hψ0,?_,hψd.comp_ofReal,implicit_root_velocity_pos ht hz,?_⟩
    · exact (hψsmooth.restrict_scalars ℝ).comp t Complex.ofRealCLM.contDiff.contDiffAt
    · have h := Complex.continuous_ofReal.continuousAt.tendsto.eventually hψroot
      filter_upwards [h] with s hs
      rw [complex_characteristic_determinant]
      simpa only [universalQuartic_real] using hs

end OscillatoryCores
