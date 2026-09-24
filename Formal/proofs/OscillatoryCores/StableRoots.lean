import proofs.OscillatoryCores.SpectrumCertificate

namespace OscillatoryCores

noncomputable def stableConstant (t : ℝ) : ℝ := a1 t*a4 t/a3 t

theorem stable_discriminant_pos {t : ℝ} (htlo : 1/2 < t) (hthi : t < 1) :
    0 < a1 t^2-4*stableConstant t := by
  have ht : 0 < t := by linarith
  have hp := coefficients_pos ht
  have ha : 100 < a1 t ∧ a1 t < 205 := by unfold a1; constructor <;> linarith
  have hb : 1 < a3 t := by unfold a3; linarith
  have hc : a4 t < 6/25 := by unfold a4; linarith
  have hprod : a1 t*a4 t < 50 := by nlinarith [hp.2.2.2]
  have hbound : stableConstant t < 50 := by
    rw [stableConstant,div_lt_iff₀ hp.2.2.1]
    nlinarith
  nlinarith [sq_nonneg (a1 t-100)]

/-- The stable factor has two distinct real negative roots. -/
theorem distinct_stable_roots {t : ℝ} (htlo : 1/2 < t) (hthi : t < 1) :
    ∃ l m : ℝ, l < m ∧ m < 0 ∧
      l^2+a1 t*l+stableConstant t=0 ∧
      m^2+a1 t*m+stableConstant t=0 := by
  have ht : 0 < t := by linarith
  have hp := coefficients_pos ht
  have hc : 0 < stableConstant t := div_pos (mul_pos hp.1 hp.2.2.2) hp.2.2.1
  let d := Real.sqrt (a1 t^2-4*stableConstant t)
  have hd : 0 < d := Real.sqrt_pos.mpr (stable_discriminant_pos htlo hthi)
  have hdsq : d^2 = a1 t^2-4*stableConstant t :=
    Real.sq_sqrt (le_of_lt (stable_discriminant_pos htlo hthi))
  have hda : d < a1 t := by nlinarith
  refine ⟨(-a1 t-d)/2,(-a1 t+d)/2,by linarith,by linarith,?_,?_⟩ <;>
    nlinarith

end OscillatoryCores
