import proofs.OscillatoryCores.SpectralCrossing

namespace OscillatoryCores

open scoped Matrix BigOperators

/-- Normalize the fourth coordinate to one. Three rows determine the
remaining coordinates; the fourth row is exactly the characteristic equation. -/
noncomputable def eigenvectorFormula (t : ℝ) (z : ℂ) : Fin 4 → ℂ :=
  let q0 := -398/(z+1)
  let q2 := (2*z+402*(t : ℂ)+(t : ℂ)*q0)/(375*(t : ℂ))
  ![q0,(1-q2)/(25*z+2),q2,1]

theorem eigenvectorFormula_fourth (t : ℝ) (z : ℂ) : eigenvectorFormula t z 3 = 1 := by
  simp [eigenvectorFormula]

set_option maxHeartbeats 800000 in
theorem eigenvectorFormula_eigen {t : ℝ} (ht : t ≠ 0) (z : ℂ)
    (h1 : z+1 ≠ 0) (h2 : 25*z+2 ≠ 0) (hz : quarticC t z = 0) :
    (normalizedJacobian t).map Complex.ofReal *ᵥ eigenvectorFormula t z =
      z • eigenvectorFormula t z := by
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have h2' : 2 + z*25 ≠ 0 := by convert h2 using 1; ring
  funext i
  fin_cases i <;>
    norm_num [normalizedJacobian,eigenvectorFormula,Matrix.mulVec,dotProduct,Fin.sum_univ_succ] <;>
    field_simp [htc,h1,h2,h2'] <;> try ring
  have hp := hz
  unfold quarticC a1 a2 a3 a4 at hp
  push_cast at hp
  field_simp [h2']
  linear_combination -6250 * hp

end OscillatoryCores
