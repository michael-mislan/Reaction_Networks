import Mathlib

namespace ProductiveChemicalHeredity

theorem forward_wait_bound : Real.exp (-(20 : ℝ)) ≤ 1/100000 := by
  have ht:=Real.sum_le_exp_of_nonneg (show (0 : ℝ)≤20 by norm_num) 8
  have hb : (100000 : ℝ)≤∑ i ∈ Finset.range 8, (20 : ℝ)^i/(i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le
    (by norm_num : (0 : ℝ)<100000) (hb.trans ht)

theorem joint_margin : (49999/50000 : ℚ)*(99957/100000)>1999/2000 := by norm_num
theorem ten_cycle_margin : (1999/2000 : ℚ)^10>995/1000 := by norm_num

end ProductiveChemicalHeredity
