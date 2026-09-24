import proofs.ThreeSitePhosphorylation.Semisimple
import proofs.ThreeSitePhosphorylation.SpectralIsolation

namespace ThreeSitePhosphorylation
noncomputable section

theorem inverse_source_intertwining (r : ℝ) :
    companionInverse*complexSource r = companionSource r*companionInverse := by
  calc
    _ = (companionInverse*complexSource r)*(companionBasis*companionInverse) := by
      rw [companion_inverse_complex_right,mul_one]
    _ = companionInverse*(complexSource r*companionBasis)*companionInverse := by
      simp only [mul_assoc]
    _ = (companionInverse*companionBasis)*companionSource r*companionInverse := by
      rw [source_companion_identity]
      simp only [mul_assoc]
    _ = _ := by rw [companion_inverse_complex,one_mul]

theorem inverse_source_action (r : ℝ) (v : Fin 9 → ℂ) :
    companionInverse.mulVec ((complexSource r).mulVec v) =
      (companionSource r).mulVec (companionInverse.mulVec v) := by
  simp only [Matrix.mulVec_mulVec,inverse_source_intertwining]

theorem inverse_source_nonzero (v : Fin 9 → ℂ) (hv : v ≠ 0) :
    companionInverse.mulVec v ≠ 0 := by
  intro hz
  have hh := congrArg companionBasis.mulVec hz
  simp only [Matrix.mulVec_mulVec,companion_inverse_complex_right,
    Matrix.one_mulVec,Matrix.mulVec_zero] at hh
  exact hv hh

theorem source_eigenvector_form (r : ℝ) (z : ℂ) (v : Fin 9 → ℂ)
    (he : (complexSource r).mulVec v = z • v) :
    v = (companionInverse.mulVec v) 0 • adjugateVector z := by
  have hh := congrArg companionInverse.mulVec he
  rw [inverse_source_action,Matrix.mulVec_smul] at hh
  have hf := companion_eigenvector_form r z (companionInverse.mulVec v) hh
  have hg := congrArg companionBasis.mulVec hf
  simpa only [Matrix.mulVec_mulVec,companion_inverse_complex_right,
    Matrix.one_mulVec,Matrix.mulVec_smul,basis_powerVector] using hg

/-- The imaginary source eigenvalue has no length-two Jordan chain. Together
with source_eigenvector_form this gives a one-dimensional, semisimple eigenspace. -/
theorem source_imaginary_no_jordan_chain (r w : ℝ) (hw : w ≠ 0)
    (v u : Fin 9 → ℂ) (hv : v ≠ 0)
    (he : (complexSource r).mulVec v = (Complex.I*(w:ℂ)) • v) :
    (complexSource r).mulVec u-(Complex.I*(w:ℂ)) • u ≠ v := by
  have hp := source_eigenvalue_root r (Complex.I*(w:ℂ)) v hv he
  have hs := candidate_imaginary_root_simple r w hw hp
  have he' := congrArg companionInverse.mulVec he
  rw [inverse_source_action,Matrix.mulVec_smul] at he'
  intro hu
  have hu' := congrArg companionInverse.mulVec hu
  rw [Matrix.mulVec_sub,inverse_source_action,Matrix.mulVec_smul] at hu'
  exact companion_no_jordan_chain r (Complex.I*(w:ℂ)) hs
    (companionInverse.mulVec v) (companionInverse.mulVec u)
    (inverse_source_nonzero v hv) he' hu'

end
end ThreeSitePhosphorylation
