import Mathlib.Analysis.Complex.ExponentialBounds

namespace ResourceLimitedCompetition

theorem log_two_population_bounds : (69/100 : ℝ) ≤ Real.log 2 ∧ Real.log 2 ≤ 7/10 := by
  constructor <;> linarith only [Real.log_two_gt_d9,Real.log_two_lt_d9]

theorem log_four_population : Real.log 4=2*Real.log 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  exact h

theorem population_endpoint_margin (N : ℝ) (hN : 0 ≤ N) :
    19*N/500000 ≤ (N/1000)*((3/5)*Real.log 4-Real.log 2-1/10) := by
  rw [log_four_population]
  have h := mul_le_mul_of_nonneg_left log_two_population_bounds.1 hN
  nlinarith only [h]

theorem population_deadline_margin (N : ℝ) (hN : 0 ≤ N) :
    -(9/5000)*N+(N/1000)*Real.log 4 ≤ -N/2500 := by
  rw [log_four_population]
  have h := mul_le_mul_of_nonneg_left log_two_population_bounds.2 hN
  nlinarith only [h]

end ResourceLimitedCompetition
