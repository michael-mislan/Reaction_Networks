import proofs.RandomViability.CollectiveOutput

namespace RandomViability
set_option maxHeartbeats 100000

theorem compensated_log_penalty :
    Real.log ((3 : ℝ)/(1/6000000000000000000 : ℝ)) < 45 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have hb : (65/24 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 65/24) hb 45
  have he : Real.exp (45 : ℝ) = (Real.exp 1)^45 := by norm_num [← Real.exp_nat_mul]
  rw [he]
  have hh : ((3 : ℝ)/(1/6000000000000000000 : ℝ)) < (65/24 : ℝ)^45 := by norm_num
  exact hh.trans_le hp

/-- Allows the small negative food shifts caused by compensation. -/
theorem compensated_endpoint_penalty (u₀ w₀ x₀ u₁ w₁ x₁ : ℝ)
    (hu : -(1/100000 : ℝ) ≤ u₀) (hw : -(1/100000 : ℝ) ≤ w₀)
    (hx₀ : (1/6000000000000000000 : ℝ) ≤ x₀)
    (hx₁ : 0 < x₁) (hxcap : x₁ ≤ 3) :
    collectivePotential u₁ w₁ x₁-collectivePotential u₀ w₀ x₀ < 54 := by
  have hdu := foodDeficit_nonneg u₀
  have hdw := foodDeficit_nonneg w₀
  have hdu1 : foodDeficit u₀ ≤ (1+1/100000 : ℝ) := max_le (by linarith only [hu]) (by norm_num)
  have hdw1 : foodDeficit w₀ ≤ (1+1/100000 : ℝ) := max_le (by linarith only [hw]) (by norm_num)
  have hlog0 := Real.log_le_log (by norm_num : (0 : ℝ) < 1/6000000000000000000) hx₀
  have hlog1 := Real.log_le_log hx₁ hxcap
  have hl := compensated_log_penalty
  rw [Real.log_div (by norm_num) (by norm_num)] at hl
  unfold collectivePotential
  nlinarith [sq_nonneg (foodDeficit u₁),sq_nonneg (foodDeficit w₁)]

/-- Final arithmetic after integration and the separate marked reward bounds.
E and B are realized export and positive basal input per volume. -/
theorem compensated_productive_margin (I E B : ℝ)
    (hI : 99*((19/10 : ℝ)-480*(1/500000000 : ℝ))-54 ≤ 640*I)
    (hE : I-(1/20 : ℝ) ≤ E)
    (hB : B ≤ 1936*(1/500000000 : ℝ)*100+1/100) :
    (1/10 : ℝ) < E ∧ B < E/4 := by
  constructor <;> linarith only [hI,hE,hB]

end RandomViability
