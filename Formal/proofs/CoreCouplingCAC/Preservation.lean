import proofs.CoreCouplingCAC.Reduction

namespace CoreCouplingCAC

theorem port_identity (p : Rates) (z : ℝ) (hz : z+2 ≠ 0) :
    z*reducedB p z = p.a+2*p.b-2*reducedB p z := by
  dsimp [reducedB]
  field_simp
  ring

theorem loss_regime_residual_increasing (p : Rates) (hp : p.Positive) (hd : 1 ≤ p.d)
    (x y : ℝ) (hx : 0 < x) (hxy : x < y) : residual p x < residual p y := by
  rcases hp with ⟨ha,hb,hu,hv,he,hdp⟩
  have hy : 0 < y := lt_trans hx hxy
  have hdx : 0 < x+2 := by linarith
  have hdy : 0 < y+2 := by linarith
  have hdd : 0 < 2+p.d := by linarith
  have hc : 0 < p.a+2*p.b := by positivity
  have hB : reducedB p y < reducedB p x := by
    dsimp [reducedB]
    apply (div_lt_div_iff₀ hdy hdx).2
    nlinarith [mul_pos hc (sub_pos.mpr hxy)]
  have hKnonneg : 0 ≤ reducedK p x := by
    dsimp [reducedK]
    apply div_nonneg _ hdd.le
    have hneg : p.u*(1-p.d)*x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hu.le (by linarith)) hx.le
    have hpos : 0 ≤ p.v*(1+2*p.d)*x^2 := by positivity
    linarith
  have hK : reducedK p x < reducedK p y := by
    have hid : reducedK p y-reducedK p x =
        (y-x)*(p.v*(1+2*p.d)*(x+y)+p.u*(p.d-1))/(2+p.d) := by
      dsimp [reducedK]
      field_simp
      ring
    apply sub_pos.mp
    rw [hid]
    have h1 : 0 < y-x := sub_pos.mpr hxy
    have h2 : 0 ≤ p.d-1 := by linarith
    positivity
  have hApos : 0 < reducedA p x := by
    dsimp [reducedA]
    have hBp : 0 < reducedB p x := div_pos hc hdx
    exact add_pos_of_pos_of_nonneg (mul_pos hx hBp) hKnonneg
  have hA : reducedA p x < reducedA p y := by
    have hi₁ := port_identity p x (ne_of_gt hdx)
    have hi₂ := port_identity p y (ne_of_gt hdy)
    dsimp [reducedA]
    linarith
  have hs : (reducedA p x)^2 < (reducedA p y)^2 := by nlinarith
  have hs' := mul_lt_mul_of_pos_left hs he
  have hb' := mul_lt_mul_of_pos_left hB (by linarith : 0 < 1+p.e)
  dsimp [residual]
  linarith

/-- A nonempty, source-derived uniqueness regime. The statement covers all
positive parameters with H loss at least one, including its boundary d=1. -/
theorem loss_regime_unistationary (p : Rates) (hp : p.Positive) (hd : 1 ≤ p.d)
    (x y : State) (hx : x.Positive) (hy : y.Positive)
    (hsx : Stationary p x) (hsy : Stationary p y) : x = y := by
  have hdx : x.z+2 ≠ 0 := by have := hx.2.2.1; positivity
  have hdy : y.z+2 ≠ 0 := by have := hy.2.2.1; positivity
  have hdd : 2+p.d ≠ 0 := by have := hp.2.2.2.2.2; positivity
  have heqx := stationary_reconstruction p x hdx hdd hsx
  have heqy := stationary_reconstruction p y hdy hdd hsy
  have hrx : residual p x.z = 0 := by
    have hb := hsx.2.1
    rw [heqx] at hb
    exact (lift_residual p x.z hdx hdd).2.1.symm.trans hb
  have hry : residual p y.z = 0 := by
    have hb := hsy.2.1
    rw [heqy] at hb
    exact (lift_residual p y.z hdy hdd).2.1.symm.trans hb
  have hz : x.z = y.z := by
    rcases lt_trichotomy x.z y.z with h | h | h
    · have hi := loss_regime_residual_increasing p hp hd x.z y.z hx.2.2.1 h
      linarith
    · exact h
    · have hi := loss_regime_residual_increasing p hp hd y.z x.z hy.2.2.1 h
      linarith
  calc
    x = lift p x.z := heqx
    _ = lift p y.z := by rw [hz]
    _ = y := heqy.symm

end CoreCouplingCAC
