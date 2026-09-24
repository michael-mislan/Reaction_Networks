import Mathlib

namespace SerialTransferSelection

/-- A coarse rational certificate suffices; no decimal logarithm evaluation. -/
theorem two_cycle_count_gain_lower :
    (519/12250 : ℝ) ≤
      2*((3/5)*Real.log 4-19/500-Real.log ((1+1/50)/(1-1/50)))-2*Real.log 2 := by
  have hlo := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hhi := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 51/49)
  have h4 : Real.log 4=2*Real.log 2 := by
    simpa only [show (2 : ℝ)^2=4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
  norm_num at hlo hhi
  norm_num only [show ((1+1/50)/(1-1/50) : ℝ)=51/49 by norm_num]
  rw [h4]
  linarith

/-- All adverse exponents in the saved u=256 instance exceed128. -/
theorem exp_negative_uniform_bound (x : ℝ) (hx : 128 ≤ x) :
    Real.exp (-x) ≤ 1/(2 : ℝ)^128 := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp : (2 : ℝ)^128 ≤ (Real.exp 1)^128 := pow_le_pow_left₀ (by norm_num) h1 128
  have he : (Real.exp 1)^128=Real.exp 128 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he] at hp
  have hm : Real.exp 128 ≤ Real.exp x := Real.exp_le_exp.mpr hx
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by positivity) (hp.trans hm)

end SerialTransferSelection
