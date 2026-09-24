import proofs.OscillatoryCores.Jacobian
import Mathlib.Analysis.Complex.Basic

namespace OscillatoryCores

open scoped Matrix

noncomputable def quarticC (t : ℝ) (z : ℂ) : ℂ :=
  z^4 + (a1 t : ℂ)*z^3 + (a2 t : ℂ)*z^2 + (a3 t : ℂ)*z + (a4 t : ℂ)

noncomputable def spectralFrequency (t : ℝ) : ℝ := Real.sqrt (a3 t / a1 t)

theorem spectralFrequency_pos {t : ℝ} (ht : 0 < t) : 0 < spectralFrequency t := by
  exact Real.sqrt_pos.mpr (div_pos (coefficients_pos ht).2.2.1 (coefficients_pos ht).1)

theorem spectralFrequency_sq {t : ℝ} (ht : 0 < t) :
    spectralFrequency t ^ 2 = a3 t / a1 t :=
  Real.sq_sqrt (le_of_lt (div_pos (coefficients_pos ht).2.2.1 (coefficients_pos ht).1))

theorem complex_crossing_factorization {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) (z : ℂ) :
    quarticC t z = (z^2 + (a3 t : ℂ)/(a1 t : ℂ)) *
      (z^2 + (a1 t : ℂ)*z + (a1 t : ℂ)*(a4 t : ℂ)/(a3 t : ℂ)) := by
  have hp := coefficients_pos ht
  have h1 : (a1 t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp.1
  have h3 : (a3 t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hp.2.2.1
  have hd : (a1 t : ℂ)*(a2 t : ℂ)*(a3 t : ℂ) - (a3 t : ℂ)^2 -
      (a1 t : ℂ)^2*(a4 t : ℂ) = 0 := by
    have h := delta3_identity t
    rw [hz,mul_zero] at h
    exact_mod_cast h
  unfold quarticC
  field_simp [h1,h3]
  linear_combination z^2*hd

theorem imaginary_quartic_root {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    quarticC t (Complex.I*(spectralFrequency t : ℂ)) = 0 := by
  rw [complex_crossing_factorization ht hz]
  have hw : (spectralFrequency t : ℂ)^2 = (a3 t : ℂ)/(a1 t : ℂ) := by
    exact_mod_cast spectralFrequency_sq ht
  simp [mul_pow,hw]

noncomputable def quarticDerivativeC (t : ℝ) (z : ℂ) : ℂ :=
  4*z^3 + 3*(a1 t : ℂ)*z^2 + 2*(a2 t : ℂ)*z + (a3 t : ℂ)

theorem quartic_hasDerivAt (t : ℝ) (z : ℂ) :
    HasDerivAt (quarticC t) (quarticDerivativeC t z) z := by
  convert (((((hasDerivAt_id z).pow 4).add
    (((hasDerivAt_id z).pow 3).const_mul (a1 t : ℂ))).add
    (((hasDerivAt_id z).pow 2).const_mul (a2 t : ℂ))).add
    ((hasDerivAt_id z).const_mul (a3 t : ℂ))).add_const (a4 t : ℂ) using 1
  simp [quarticDerivativeC]
  ring

theorem imaginary_root_simple {t : ℝ} (ht : 0 < t) :
    quarticDerivativeC t (Complex.I*(spectralFrequency t : ℂ)) ≠ 0 := by
  have hp := coefficients_pos ht
  have hw : a1 t * spectralFrequency t ^ 2 = a3 t := by
    rw [spectralFrequency_sq ht]
    field_simp [ne_of_gt hp.1]
  intro hz
  have hr := congrArg Complex.re hz
  norm_num [quarticDerivativeC,pow_succ,Complex.mul_re,Complex.mul_im] at hr
  nlinarith

/-- The other quadratic factor has strictly negative real parts. -/
theorem positive_quadratic_roots_left {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {z : ℂ} (hz : z^2+(a : ℂ)*z+(c : ℂ)=0) : z.re < 0 := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im,
    pow_two,Complex.ofReal_re,Complex.ofReal_im,Complex.zero_re,Complex.zero_im,
    zero_mul,sub_zero,add_zero] at hr hi
  by_cases hy : z.im = 0
  · rw [hy] at hr
    by_contra hx
    have hx0 : 0 ≤ z.re := le_of_not_gt hx
    have hax := mul_nonneg ha.le hx0
    nlinarith [sq_nonneg z.re]
  · have he : z.im*(2*z.re+a)=0 := by nlinarith [hi]
    have he' := (mul_eq_zero.mp he).resolve_left hy
    linarith

set_option maxHeartbeats 800000 in
theorem complex_characteristic_determinant (t : ℝ) (z : ℂ) :
    (z • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
      (normalizedJacobian t).map Complex.ofReal).det = quarticC t z := by
  have he : z • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
      (normalizedJacobian t).map Complex.ofReal =
      !![z+1,0,0,398; 0,z+2/25,1/25,-1/25;
        -2/375,2/125,z+251/125,-801/375;
        (t : ℂ)/2,0,-375*(t : ℂ)/2,z+201*(t : ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [normalizedJacobian] <;> ring
  rw [he,Matrix.det_succ_row_zero]
  norm_num [Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.submatrix_apply,
    Matrix.cons_val_two,Matrix.cons_val_three,Fin.castSucc,Fin.castAdd,Fin.castLE,
    quarticC,a1,a2,a3,a4]
  ring

theorem imaginary_jacobian_root {t : ℝ} (ht : 0 < t)
    (hz : crossingPolynomial t = 0) :
    ((Complex.I*(spectralFrequency t : ℂ)) • (1 : Matrix (Fin 4) (Fin 4) ℂ) -
      (normalizedJacobian t).map Complex.ofReal).det = 0 := by
  rw [complex_characteristic_determinant]
  exact imaginary_quartic_root ht hz

end OscillatoryCores
