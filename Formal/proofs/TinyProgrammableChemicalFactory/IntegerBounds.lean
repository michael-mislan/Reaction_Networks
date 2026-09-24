import Mathlib

namespace TinyProgrammableChemicalFactory

theorem repair_exponential_bound : Real.exp (-(56 : ℝ)) ≤ 1/1000000 := by
  have ht:=Real.sum_le_exp_of_nonneg (show (0 : ℝ)≤56 by norm_num) 6
  have hb : (1000000 : ℝ)≤∑ i ∈ Finset.range 6, (56 : ℝ)^i/(i.factorial : ℝ) := by
    norm_num [Finset.sum_range_succ]
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1000000) (hb.trans ht)

theorem concrete_budget :
    (2147232289 : ℚ)/2147483648-15/1000000 > 4999/5000 := by norm_num

theorem ten_cycle_budget : (4999/5000 : ℚ)^10 > 998/1000 := by norm_num

theorem extra_hazard_budget : (80 : ℚ)/10^9+80^3/10^12 < 1/10^6 := by norm_num

theorem suppressed_prefix_budget :
    (2*80^2+2*80^2/100 : ℚ)+80/10^9+80^3/10^12 <13000 := by norm_num

/-- Natural-number quotient rounding is downward, including its scaling. -/
theorem quotient_lower (a d : ℕ) : a/d*d≤a := Nat.div_mul_le_self a d

theorem core_machine_bounds :
    (321600 : ℕ)*2^31<2^63 ∧ (2^31 : ℕ)*2147483643<2^63 := by norm_num

end TinyProgrammableChemicalFactory
