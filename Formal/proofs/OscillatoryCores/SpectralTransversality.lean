import proofs.OscillatoryCores.SpectralCrossing
import Mathlib.Analysis.Complex.RealDeriv

namespace OscillatoryCores

noncomputable def quarticParameterDerivativeC (z : ℂ) : ℂ :=
  201*z^3 + (5297/250 : ℂ)*z^2 + (479/250 : ℂ)*z + 6/25

theorem quartic_parameter_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (fun s : ℝ => quarticC s z) (quarticParameterDerivativeC z) t := by
  have heq : (fun s : ℝ => quarticC s z) =
      (fun s : ℝ => quarticC 0 z + (s : ℂ)*quarticParameterDerivativeC z) := by
    funext s
    unfold quarticC quarticParameterDerivativeC a1 a2 a3 a4
    push_cast
    ring
  rw [heq]
  simpa using (Complex.ofRealCLM.hasDerivAt.mul_const (quarticParameterDerivativeC z)).const_add
    (quarticC 0 z)

private theorem crossing_numerator_pos
    (a b c d ap bp cp dp s : ℝ) (ha : 0 < a) (hs : 0 < s)
    (hcs : c-a*s=0) (hd : a*b*c-c^2-a^2*d=0)
    (hdelta : ap*b*c+a*bp*c+a*b*cp-2*c*cp-2*a*ap*d-a^2*dp < 0) :
    0 < 2*c*(dp-bp*s)-2*s*(cp-ap*s)*(b-2*s) := by
  let N := 2*c*(dp-bp*s)-2*s*(cp-ap*s)*(b-2*s)
  let Δ := ap*b*c+a*bp*c+a*b*cp-2*c*cp-2*a*ap*d-a^2*dp
  have hid : a^2*N + 2*a*s*Δ =
      (c-a*s)*(2*a^2*dp-4*a*s*cp+2*s*ap*(-a*b+2*(c+a*s))) +
        4*s*ap*(a*b*c-c^2-a^2*d) := by dsimp [N,Δ]; ring
  rw [hcs,hd] at hid
  have heq : a^2*N = -(2*a*s*Δ) := by linarith
  have hp : 0 < a^2*N := by
    rw [heq]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (by positivity) hdelta)
  exact (mul_pos_iff_of_pos_left (sq_pos_of_pos ha)).mp hp

/-- The algebraic implicit-root velocity has positive real part. This is
the transversality quantity -P_t/P_z at the authenticated simple imaginary root. -/
theorem implicit_root_velocity_pos {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    0 < (-quarticParameterDerivativeC (Complex.I*(spectralFrequency t : ℂ)) /
      quarticDerivativeC t (Complex.I*(spectralFrequency t : ℂ))).re := by
  let w := spectralFrequency t
  have hw : 0 < w := spectralFrequency_pos ht
  have ha : 0 < a1 t := (coefficients_pos ht).1
  have hc : a3 t-a1 t*w^2=0 := by
    dsimp [w]
    rw [spectralFrequency_sq ht]
    field_simp [ne_of_gt ha]
    ring
  have hd := delta3_identity t
  rw [hz,mul_zero] at hd
  have hdelta : 201*a2 t*a3 t+a1 t*(5297/250)*a3 t+a1 t*a2 t*(479/250)-
      2*a3 t*(479/250)-2*a1 t*201*a4 t-(a1 t)^2*(6/25) < 0 := by
    have heq : 201*a2 t*a3 t+a1 t*(5297/250)*a3 t+a1 t*a2 t*(479/250)-
        2*a3 t*(479/250)-2*a1 t*201*a4 t-(a1 t)^2*(6/25) =
        3/7812500*crossingSlope t := by unfold a1 a2 a3 a4 crossingSlope; ring
    rw [heq]
    exact mul_neg_of_pos_of_neg (by norm_num) (crossingSlope_negative ht hz)
  have hN := crossing_numerator_pos (a1 t) (a2 t) (a3 t) (a4 t)
    201 (5297/250) (479/250) (6/25) (w^2) ha (sq_pos_of_pos hw) hc hd hdelta
  have hP : quarticDerivativeC t (Complex.I*(w : ℂ)) =
      (-2*a3 t : ℝ) + Complex.I*(2*w*(a2 t-2*w^2) : ℝ) := by
    apply Complex.ext <;>
      norm_num [quarticDerivativeC,pow_succ,Complex.mul_re,Complex.mul_im]
    · nlinarith [hc]
    · ring
  have hT : -quarticParameterDerivativeC (Complex.I*(w : ℂ)) =
      (-(6/25)+(5297/250)*w^2 : ℝ) +
        Complex.I*(-w*((479/250)-201*w^2) : ℝ) := by
    apply Complex.ext <;>
      norm_num [quarticParameterDerivativeC,pow_succ,Complex.mul_re,Complex.mul_im]
    ring
  have hden : 0 < Complex.normSq (quarticDerivativeC t (Complex.I*(w : ℂ))) :=
    Complex.normSq_pos.mpr (imaginary_root_simple ht)
  change 0 < (-quarticParameterDerivativeC (Complex.I*(w : ℂ)) /
    quarticDerivativeC t (Complex.I*(w : ℂ))).re
  rw [Complex.div_re,hT]
  rw [hP]
  norm_num only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_add,add_zero,sub_zero]
  rw [← add_div]
  apply div_pos _ (by simpa only [hP] using hden)
  convert hN using 1
  ring

end OscillatoryCores
