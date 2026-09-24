import proofs.ProductiveMemory.ExtractionInterval

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

def boundaryNumerator (z : ℝ) : ℝ :=
  let y := z-5/2
  2646507285317916225/16-(373906577279071365/2)*y+
    (61291592184661597047/2)*y^2+26834156547533132606*y^3+
    4448592406875058329*y^4+136356292472000*y^5+44462224000000*y^6

theorem boundary_numerator_identity (z : ℝ) (hz : z+2 ≠ 0) :
    residual (31/1000) z*(4444888900000000000*(z+2)^2)=boundaryNumerator z := by
  unfold residual reducedA reducedB reducedK boundaryNumerator
  field_simp [hz]
  ring

theorem boundary_numerator_positive (z : ℝ) (hz : 2 ≤ z) : 0 < boundaryNumerator z := by
  let y := z-5/2
  have hy : 0 ≤ y+1/2 := by dsimp [y]; linarith only [hz]
  have hquad : 0 < (2646507285317916225/16:ℝ)-(373906577279071365/2)*y+
      (34457435637128464441/2)*y^2 := by
    nlinarith only [sq_nonneg ((34457435637128464441:ℝ)*y-373906577279071365/2)]
  have hid : boundaryNumerator z =
      ((2646507285317916225/16:ℝ)-(373906577279071365/2)*y+(34457435637128464441/2)*y^2)+
      26834156547533132606*(y+1/2)*y^2+
      4448524228728822329*y^4+136356292472000*(y+1/2)*y^4+44462224000000*y^6 := by
    unfold boundaryNumerator
    dsimp [y]
    ring
  rw [hid]
  positivity

theorem boundary_residual_positive (rho z : ℝ) (hr : 31/1000 ≤ rho) (hz : 2 ≤ z) :
    0 < residual rho z := by
  have hp := boundary_numerator_positive z hz
  have hid := boundary_numerator_identity z (by linarith)
  have hd : 0 < (4444888900000000000:ℝ)*(z+2)^2 := by
    have hzpos : 0 < z+2 := by linarith
    positivity
  have hlow : 0 < residual (31/1000) z := (mul_pos_iff_of_pos_right hd).mp (hid.symm ▸ hp)
  exact hlow.trans_le (residual_rate_mono (31/1000) rho z (by norm_num) hr (by linarith))

/-- A stationary high-state exclusion, not a finite-horizon memory-loss claim. -/
theorem no_high_stationary_above_boundary (rho : ℝ) (hr : 31/1000 ≤ rho) (x : Point)
    (hz : 2 ≤ x 2) : extractDrift rho 0 x ≠ 0 := by
  intro hx
  have hzero := ((stationary_iff rho x (by linarith)).mp hx).2
  have hp := boundary_residual_positive rho (x 2) hr hz
  linarith only [hzero,hp]

end
end ProductiveMemory
