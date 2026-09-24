import proofs.OscillatoryCores.EigenvectorFormula
import proofs.OscillatoryCores.SpectrumCertificate
import proofs.OscillatoryCores.SpectralModes

namespace OscillatoryCores

open Filter
open scoped ContDiff Topology Matrix BigOperators

theorem eigenvectorFormula_contDiffAt {t : ℝ} {eig : ℝ → ℂ}
    (he : ContDiffAt ℝ ∞ eig t) (ht : t ≠ 0)
    (h1 : eig t+1 ≠ 0) (h2 : 25*eig t+2 ≠ 0) :
    ContDiffAt ℝ ∞ (fun s => eigenvectorFormula s (eig s)) t := by
  have hc : ContDiffAt ℝ ∞ (fun s : ℝ => (s : ℂ)) t :=
    Complex.ofRealCLM.contDiff.contDiffAt
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hq0 : ContDiffAt ℝ ∞ (fun s => (-398 : ℂ)/(eig s+1)) t := by
    simpa only [div_eq_mul_inv] using
      contDiffAt_const.mul ((he.add contDiffAt_const).inv h1)
  have hq2 : ContDiffAt ℝ ∞
      (fun s => (2*eig s+402*(s : ℂ)+(s : ℂ)*(-398/(eig s+1)))/(375*(s : ℂ))) t := by
    simpa only [div_eq_mul_inv] using
      (((contDiffAt_const.mul he).add (contDiffAt_const.mul hc)).add
        (hc.mul hq0)).mul ((contDiffAt_const.mul hc).inv (mul_ne_zero (by norm_num) htc))
  have hq1 : ContDiffAt ℝ ∞
      (fun s => (1-(2*eig s+402*(s : ℂ)+(s : ℂ)*(-398/(eig s+1)))/(375*(s : ℂ)))/(25*eig s+2)) t := by
    simpa only [div_eq_mul_inv] using
      (contDiffAt_const.sub hq2).mul (((contDiffAt_const.mul he).add contDiffAt_const).inv h2)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hq0
  · exact hq1
  · exact hq2
  · exact contDiffAt_const

theorem complex_eigenvector_real_modes (t : ℝ) (z : ℂ) (q : Fin 4 → ℂ)
    (hq : (normalizedJacobian t).map Complex.ofReal *ᵥ q = z • q) :
    normalizedLinear t (fun i => (q i).re) =
      z.re • (fun i => (q i).re) - z.im • (fun i => (q i).im) ∧
    normalizedLinear t (fun i => (q i).im) =
      z.im • (fun i => (q i).re) + z.re • (fun i => (q i).im) := by
  constructor
  · rw [normalizedLinear_apply]
    funext i
    have h := congrArg (fun v : Fin 4 → ℂ => (v i).re) hq
    simpa [Matrix.mulVec,dotProduct,Complex.mul_re] using h
  · rw [normalizedLinear_apply]
    funext i
    have h := congrArg (fun v : Fin 4 → ℂ => (v i).im) hq
    simpa [Matrix.mulVec,dotProduct,Complex.mul_im,add_comm] using h

end OscillatoryCores
