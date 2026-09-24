import proofs.TinyProgrammableChemicalFactory.IntegerBounds

namespace TinyProgrammableChemicalFactory

theorem integer_prefix_max (r : ℤ) : 15999*r-199*r^2≤321560 := by
  by_cases h : r≤40
  · have h1 : 0≤40-r := by omega
    have h2 : 0≤8039-199*r := by omega
    nlinarith [mul_nonneg h1 h2]
  · have h1 : 0≤r-40 := by omega
    have h2 : 0≤199*r-8039 := by omega
    nlinarith [mul_nonneg h1 h2]

theorem refined_repair_exponential : Real.exp (-(14 : ℝ))≤1/1000000 := by
  have ht:=Real.sum_le_exp_of_nonneg (show (0 : ℝ)≤14 by norm_num) 19
  have hb : (1000000 : ℝ)≤∑ i ∈ Finset.range 19, (14 : ℝ)^i/(i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1000000) (hb.trans ht)

theorem enlarged_box_budget :
    (2147232289 : ℚ)/2147483648 - (1/10^6+3216/80000000+80/10^7+80^3*6/10^11)
      >4999/5000 := by norm_num

theorem imperfect_operation_budget :
    (2147153442 : ℚ)/2147483648 - (1/10^6+3216/400000000+80/10^8+80^3/10^11)
      >4999/5000 := by norm_num

end TinyProgrammableChemicalFactory
