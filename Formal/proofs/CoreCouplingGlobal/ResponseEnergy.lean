import Mathlib

namespace CoreCouplingGlobal

/-- The cross terms in the response coordinates admit an exact square decomposition. -/
theorem response_energy_identity (a c m w r F Z K n : ℝ)
    (hm : m ≠ 0) (hw : w ≠ 0) :
    -m*F^2-Z^2/w-n*K^2-a*(1+c)*r^2-(a*m+c)*r*F-r*Z/w =
      -(m/2)*F^2-Z^2/(2*w)-n*K^2
      -(a*(1+c)-a^2*m-c^2/m-1/(2*w))*r^2
      -m*(F/2+a*r)^2-(m*F/2+c*r)^2/m-(Z+r)^2/(2*w) := by
  field_simp
  ring

theorem response_coefficient_bound (a c m w : ℝ)
    (ha : 99/100 ≤ a) (ha' : a ≤ 101/100)
    (hc : -(1/500) ≤ c) (hc' : c ≤ 1/500)
    (hm : 1/500 ≤ m) (hm' : m ≤ 13/50) (hw : 2 ≤ w) :
    (1/4:ℝ) ≤ a*(1+c)-a^2*m-c^2/m-1/(2*w) := by
  have hm0 : 0 < m := by linarith
  have hw0 : 0 < w := by linarith
  have ha0 : 0 ≤ a := by linarith
  have hprod : (99/100:ℝ)*(499/500) ≤ a*(1+c) :=
    mul_le_mul ha (by linarith) (by norm_num) ha0
  have ha2 : a^2 ≤ (101/100:ℝ)^2 := by nlinarith
  have hma : a^2*m ≤ (101/100:ℝ)^2*(13/50) :=
    mul_le_mul ha2 hm' (le_of_lt hm0) (by norm_num)
  have hc2 : c^2 ≤ (1/500:ℝ)^2 := by nlinarith
  have hcm : c^2/m ≤ (1/500:ℝ) := (div_le_iff₀ hm0).2 (by nlinarith)
  have hwi : 1/(2*w) ≤ (1/4:ℝ) :=
    (div_le_iff₀ (by positivity : 0 < 2*w)).2 (by linarith)
  linarith

/-- Uniform strict dissipation once the response gradients satisfy their scalar bounds. -/
theorem response_energy_dissipation (a c m w r F Z K n : ℝ)
    (ha : 99/100 ≤ a) (ha' : a ≤ 101/100)
    (hc : -(1/500) ≤ c) (hc' : c ≤ 1/500)
    (hm : 1/500 ≤ m) (hm' : m ≤ 13/50)
    (hw : 2 ≤ w) (hw' : w ≤ 182) (hn : 1/4000 ≤ n) :
    -m*F^2-Z^2/w-n*K^2-a*(1+c)*r^2-(a*m+c)*r*F-r*Z/w ≤
      -r^2/4-F^2/1000-Z^2/364-K^2/4000 := by
  have hm0 : 0 < m := by linarith
  have hw0 : 0 < w := by linarith
  have hb := response_coefficient_bound a c m w ha ha' hc hc' hm hm' hw
  have hr := mul_le_mul_of_nonneg_right hb (sq_nonneg r)
  have hF := mul_le_mul_of_nonneg_right hm (sq_nonneg F)
  have hK := mul_le_mul_of_nonneg_right hn (sq_nonneg K)
  have hZ : Z^2/364 ≤ Z^2/(2*w) :=
    div_le_div_of_nonneg_left (sq_nonneg Z) (by positivity) (by linarith)
  have hs₁ := mul_nonneg (le_of_lt hm0) (sq_nonneg (F/2+a*r))
  have hs₂ := div_nonneg (sq_nonneg (m*F/2+c*r)) (le_of_lt hm0)
  have hs₃ := div_nonneg (sq_nonneg (Z+r)) (by positivity : 0 ≤ 2*w)
  rw [response_energy_identity a c m w r F Z K n (ne_of_gt hm0) (ne_of_gt hw0)]
  nlinarith only [hr,hF,hK,hZ,hs₁,hs₂,hs₃]

end CoreCouplingGlobal
