import proofs.ResourceLimitedCompetition.GainProbability
import proofs.ResourceLimitedCompetition.EndpointOdds
namespace ResourceLimitedCompetition
theorem endpoint_gain_barrier (gain : ℝ) (N H0 L0 H L : ℕ)
    (hH0 : 0 < H0) (hL0 : 0 < L0) (hH : 0 < H) (hL : 0 < L)
    (hw : H+L=4*(H0+L0))
    (hr : Real.log H-Real.log L-(Real.log H0-Real.log L0) ≤ Real.log 2+gain) :
    Real.exp (((N : ℝ)/1000)*((3/5)*Real.log 4-Real.log 2-gain)) ≤ oddsValue N H0 L0 H L := by
  rw [oddsValue_exponential N H0 L0 H L hH hL]
  have hsum : 0 < (H0 : ℝ)+L0 := by positivity
  have htotal : Real.log ((H : ℝ)+L)-Real.log ((H0 : ℝ)+L0)=Real.log 4 := by
    have hwR : (H : ℝ)+L=4*((H0 : ℝ)+L0) := by exact_mod_cast hw
    rw [hwR,Real.log_mul (by norm_num) (ne_of_gt hsum)]
    ring
  rw [htotal]
  apply Real.exp_le_exp.mpr
  have hscaled := mul_le_mul_of_nonneg_left hr (by positivity : 0 ≤ (N : ℝ)/1000)
  nlinarith only [hscaled]
theorem membrane_odds_log_bound_gain (gain : ℝ) (H0 L0 H L : ℝ)
    (hH0 : 0 < H0) (hL0 : 0 < L0) (hH : 0 < H) (hL : 0 < L)
    (hprod : H*L0 ≤ (2*Real.exp gain)*(H0*L)) :
    Real.log H-Real.log L-(Real.log H0-Real.log L0) ≤ Real.log 2+gain := by
  have h := Real.log_le_log (mul_pos hH hL0) hprod
  rw [Real.log_mul (ne_of_gt hH) (ne_of_gt hL0),
    Real.log_mul (ne_of_gt (by positivity : 0 < 2*Real.exp gain)) (ne_of_gt (mul_pos hH0 hL)),
    Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)),Real.log_exp,
    Real.log_mul (ne_of_gt hH0) (ne_of_gt hL)] at h
  linarith only [h]

theorem count_to_membrane_odds_gain (gain : ℝ) (N h l H L cH cL : ℕ)
    (hH : H ≤ 2*N*cH) (hL : N*cL ≤ L)
    (hbad : (cH : ℝ)*l ≤ Real.exp gain*(h : ℝ)*cL) :
    (H : ℝ)*(N*l : ℕ) ≤ (2*Real.exp gain)*((N*h : ℕ)*(L : ℝ)) := by
  have hHR : (H : ℝ) ≤ 2*(N : ℝ)*cH := by exact_mod_cast hH
  have hLR : (N : ℝ)*cL ≤ L := by exact_mod_cast hL
  have h1 := mul_le_mul_of_nonneg_right hHR (by positivity : 0 ≤ (N : ℝ)*l)
  have h2 := mul_le_mul_of_nonneg_left hbad (by positivity : 0 ≤ 2*(N : ℝ)^2)
  have h3 := mul_le_mul_of_nonneg_left hLR (by positivity : 0 ≤ 2*Real.exp gain*((N : ℝ)*h))
  simp only [Nat.cast_mul]
  nlinarith only [h1,h2,h3]


end ResourceLimitedCompetition
