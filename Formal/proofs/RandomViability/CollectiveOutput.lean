import proofs.RandomViability.CollectiveCalculus
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 20000

namespace RandomViability

theorem collective_log_penalty :
    Real.log ((11/4:ℝ)/(1/3000000000000000000:ℝ)) < 44 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have hbase : (65/24:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 65/24) hbase 44
  have he : Real.exp (44:ℝ) = (Real.exp 1)^44 := by
    norm_num [← Real.exp_nat_mul]
  rw [he]
  have hnum : ((11/4:ℝ)/(1/3000000000000000000:ℝ)) < (65/24:ℝ)^44 := by norm_num
  exact hnum.trans_le hp

theorem collective_endpoint_penalty (u₀ w₀ x₀ u₁ w₁ x₁ : ℝ)
    (hu : 0 ≤ u₀) (hw : 0 ≤ w₀)
    (hx₀ : (1/3000000000000000000:ℝ) ≤ x₀)
    (hx₁ : 0 < x₁) (hxcap : x₁ ≤ 11/4) :
    collectivePotential u₁ w₁ x₁-collectivePotential u₀ w₀ x₀ < 52 := by
  have hdu := foodDeficit_nonneg u₀
  have hdw := foodDeficit_nonneg w₀
  have hdu1 := foodDeficit_le_one u₀ hu
  have hdw1 := foodDeficit_le_one w₀ hw
  have hlog0 := Real.log_le_log (by norm_num : (0:ℝ) < 1/3000000000000000000) hx₀
  have hlog1 := Real.log_le_log hx₁ hxcap
  have hl := collective_log_penalty
  rw [Real.log_div (by norm_num) (by norm_num)] at hl
  unfold collectivePotential
  nlinarith [sq_nonneg (foodDeficit u₁), sq_nonneg (foodDeficit w₁)]

/-- Once startup and the integrated corrected-growth certificate hold, export
minus the positive basal budget exceeds 0.23. Both are physical mass units per
volume; the signed balance must be attached separately to identify currents. -/
theorem collective_finite_horizon_output (P dP M : ℝ → ℝ) (J : ℝ)
    (hP : ∀ t ∈ Set.Icc (1:ℝ) 100, HasDerivAt P (dP t) t)
    (hM : ContinuousOn M (Set.Icc (1:ℝ) 100))
    (hbound : ∀ t ∈ Set.Ioo (1:ℝ) 100,
      2-468*(1/500000000:ℝ)-624*M t ≤ dP t)
    (hpenalty : P 100-P 1 ≤ 52)
    (hJ : J ≤ 1936*(1/500000000:ℝ)*100) :
    23/100 < (∫ t in (1:ℝ)..100, M t)-J := by
  have hi := collective_integrated_growth P dP M 1 100 (1/500000000)
    (by norm_num) hP hM hbound
  apply collective_integrated_margin _ J _ hJ
  linarith

end RandomViability
