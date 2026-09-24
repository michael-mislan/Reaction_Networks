import proofs.OscillatoryCores.SpectralModes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace OscillatoryCores

noncomputable def centerCurve (u v : State) (w s : ℝ) : State :=
  Real.cos (w*s) • u - Real.sin (w*s) • v

theorem centerCurve_hasDerivAt (t : ℝ) (u v : State) (w s : ℝ)
    (hu : normalizedLinear t u = -w • v)
    (hv : normalizedLinear t v = w • u) :
    HasDerivAt (centerCurve u v w)
      (normalizedLinear t (centerCurve u v w s)) s := by
  have ha : HasDerivAt (fun s : ℝ => w*s) w s := by
    simpa using (hasDerivAt_id s).const_mul w
  convert (ha.cos.smul_const u).sub (ha.sin.smul_const v) using 1
  simp only [centerCurve,map_sub,map_smul,hu,hv,smul_smul]
  module

theorem centerCurve_periodic (u v : State) {w : ℝ} (hw : w ≠ 0) :
    Function.Periodic (centerCurve u v w) (2*Real.pi/w) := by
  intro s
  have he : w*(s+2*Real.pi/w)=w*s+2*Real.pi := by field_simp
  simp [centerCurve,he]

theorem centerCurve_nonconstant (u v : State) (hu : u ≠ 0) {w : ℝ} (hw : w ≠ 0) :
    ∃ s, centerCurve u v w s ≠ centerCurve u v w 0 := by
  refine ⟨Real.pi/w,?_⟩
  have he : w*(Real.pi/w)=Real.pi := by field_simp
  intro h
  have hneg : -u = u := by simpa [centerCurve,he] using h
  apply hu
  funext i
  have hi := congrFun hneg i
  change -(u i) = u i at hi
  change u i = 0
  linarith

/-- The nonconstant base orbit belongs to the linear, zero-amplitude
equation. It is the base point for shooting, not the nonlinear source conclusion. -/
theorem linear_center_orbit_exists {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    ∃ y : ℝ → State, ∃ T : ℝ, 0 < T ∧ Function.Periodic y T ∧
      (∀ s, HasDerivAt y (normalizedLinear t (y s)) s) ∧
      (∃ s, y s ≠ y 0) := by
  obtain ⟨u,v,hu,hAu,hAv⟩ := real_center_modes ht hz
  have hw := spectralFrequency_pos ht
  refine ⟨centerCurve u v (spectralFrequency t),2*Real.pi/spectralFrequency t,
    by positivity,centerCurve_periodic u v (ne_of_gt hw),?_,
    centerCurve_nonconstant u v hu (ne_of_gt hw)⟩
  intro s
  exact centerCurve_hasDerivAt t u v (spectralFrequency t) s hAu hAv

end OscillatoryCores
