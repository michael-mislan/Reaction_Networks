import proofs.CompositionalMemory.SemenovFieldTaylor

namespace CompositionalMemory.Semenov
open Polynomial

theorem qsingleton_value (q : ℚ) (t : ℝ) : aeval t (qpolynomial [q])=(q : ℝ) := by
  simp only [qpolynomial,mul_zero,add_zero,aeval_C]
  rfl

theorem kinetic_algebraMap (r : Fin 11) : (algebraMap ℚ ℝ) (kineticRational r)=nominalRate r :=
  kineticRational_cast r

theorem chemical_derivative_polynomial_value (z : Fin 8 → QCoefficients)
    (r : Fin 11) (j : Fin 8) (t : ℝ) :
    aeval t (qpolynomial (chemicalDerivativePolynomial z r j))=
      chemicalDerivativeValue (fun i => aeval t (qpolynomial (z i))) r j := by
  unfold chemicalDerivativePolynomial chemicalDerivativeValue
  split_ifs <;>
    simp only [qpolynomial_qadd,qpolynomial_qscale,map_add,map_mul,aeval_C,kinetic_algebraMap,
      qpolynomial,map_zero,mul_zero,add_zero,zero_add]

theorem jacobian_polynomial_value (z : Fin 8 → QCoefficients) (i j : Fin 8) (t : ℝ) :
    aeval t (qpolynomial (jacobianPolynomial z i j))=
      jacobianValue (fun k => aeval t (qpolynomial (z k))) i j := by
  simp only [jacobianPolynomial,qpolynomial_qadd,qpolynomial_qsumFin,qpolynomial_qscale,
    map_add,map_sum,map_mul,aeval_C,chemical_derivative_polynomial_value,qsingleton_value]
  norm_num only [map_intCast]
  unfold jacobianValue
  congr 1
  split_ifs <;> norm_num

noncomputable def timePolynomialValue (p : QCoefficients) (scale : ℚ) (t : ℝ) : ℝ :=
  aeval (-1+(scale : ℝ)*t) (qpolynomial p)

theorem time_polynomial_derivative (p : QCoefficients) (scale : ℚ) (t : ℝ) :
    HasDerivAt (timePolynomialValue p scale)
      ((scale : ℝ)*timePolynomialValue (qderivative p) scale t) t := by
  have ha : HasDerivAt (fun u : ℝ => -1+(scale : ℝ)*u) (scale : ℝ) t := by
    simpa only [mul_one,zero_add] using
      (hasDerivAt_const t (-1 : ℝ)).add ((hasDerivAt_id t).const_mul (scale : ℝ))
  have hh := ((qpolynomial p).hasDerivAt_aeval (-1+(scale : ℝ)*t)).comp t ha
  unfold timePolynomialValue
  rw [qpolynomial_qderivative]
  convert hh using 1
  ring

theorem normalized_time_mem (duration scale t : ℝ) (hd : 0 < duration)
    (hs : scale=2/duration) (ht : t ∈ Set.Icc (0 : ℝ) duration) :
    -1+scale*t ∈ Set.Icc (-1 : ℝ) 1 := by
  have hscale : 0 < scale := by rw [hs]; positivity
  have he : scale*duration=2 := by rw [hs]; field_simp
  have hlo := mul_nonneg hscale.le ht.1
  have hhi := mul_le_mul_of_nonneg_left ht.2 hscale.le
  constructor <;> linarith only [hlo,hhi,he]

end CompositionalMemory.Semenov
