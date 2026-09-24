import Mathlib.Tactic

namespace RandomViability

/-- Resource deficit used by the collective-production certificate. -/
def foodDeficit (u : ℝ) : ℝ := max (1 - u) 0

theorem foodDeficit_nonneg (u : ℝ) : 0 ≤ foodDeficit u := le_max_right _ _

theorem foodDeficit_le_one (u : ℝ) (hu : 0 ≤ u) : foodDeficit u ≤ 1 := by
  exact max_le (by linarith) (by norm_num)

theorem foodDeficit_resource (u : ℝ) : 1 - foodDeficit u ≤ u := by
  have h : 1 - u ≤ foodDeficit u := le_max_left _ _
  linarith

/-- The square correction controls the food loss, including the corner u=1.
The expression on the left is the derivative of the squared deficit. -/
theorem deficit_drift (u du c : ℝ) (hc : 0 ≤ c)
    (hdu : 1 - u - 23 * c * u ≤ du) :
    -2 * foodDeficit u * du ≤ -2 * (foodDeficit u)^2 + (23 / 2) * c := by
  by_cases h : u ≤ 1
  · have hd : foodDeficit u = 1 - u := max_eq_left (by linarith)
    rw [hd]
    have hm := mul_le_mul_of_nonneg_left hdu (show 0 ≤ 2 * (1-u) by linarith)
    have hs := mul_nonneg hc (sq_nonneg (u - 1/2))
    nlinarith
  · have hd : foodDeficit u = 0 := max_eq_right (by linarith)
    rw [hd]
    nlinarith

theorem food_product_deficit (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    3 / 4 - 2 * ((foodDeficit u)^2 + (foodDeficit w)^2) ≤ u*w := by
  have hdu := foodDeficit_nonneg u
  have hdw := foodDeficit_nonneg w
  have hlu := foodDeficit_le_one u hu
  have hlw := foodDeficit_le_one w hw
  have hp := mul_le_mul (foodDeficit_resource u) (foodDeficit_resource w)
    (show 0 ≤ 1 - foodDeficit w by linarith) hu
  have hde := mul_nonneg hdu hdw
  nlinarith [sq_nonneg (foodDeficit u - 1/4), sq_nonneg (foodDeficit w - 1/4)]

/-- Algebraic full-host corrected-growth implication. The three coordinate
drift hypotheses must be proved for the literal reactor separately. -/
theorem collective_corrected_growth (u w x du dw dx eps M : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 < x)
    (heps : 0 ≤ eps) (hM : 0 ≤ M)
    (hdu : 1-u-23*(4*eps+(16/3)*M)*u ≤ du)
    (hdw : 1-w-23*(4*eps+(16/3)*M)*w ≤ dw)
    (hdx : eps*u*w+x*(4*u*w-1-25*(4*eps+(16/3)*M)) ≤ dx) :
    2-468*eps-624*M ≤
      dx/x - 4*(-2*foodDeficit u*du-2*foodDeficit w*dw) := by
  have hc : 0 ≤ 4*eps+(16/3)*M := by positivity
  have h1 := deficit_drift u du _ hc hdu
  have h2 := deficit_drift w dw _ hc hdw
  have hp := food_product_deficit u w hu hw
  have hb : 0 ≤ eps*u*w := by positivity
  have hl : 4*u*w-1-25*(4*eps+(16/3)*M) ≤ dx/x := by
    apply (le_div_iff₀ hx).2
    nlinarith
  linarith

/-- Exact deterministic integrated margin, after the endpoint penalty has
been bounded by 52 and the basal budget by 1936 eps times 100. -/
theorem collective_integrated_margin (I J : ℝ)
    (hI : 99*(2-468*(1/500000000:ℝ))-52 ≤ 624*I)
    (hJ : J ≤ 1936*(1/500000000:ℝ)*100) :
    23/100 < I-J := by linarith

end RandomViability
