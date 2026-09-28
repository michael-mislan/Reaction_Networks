import proofs.StartupCount.LogOccupation
import Mathlib.Analysis.Complex.ExponentialBounds

namespace StartupCount
open RandomViability

/-- Exact minimum of the food/count combination: the completed square
`16/5 + 5(α+β-2/5)^2 + 3(α-β)^2` with `α,β` the two food deficits. -/
theorem food_product_deficit_sharp (u w : ℝ) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    16/5 ≤ 4*(u*w)+8*((foodDeficit u)^2+(foodDeficit w)^2) := by
  have hlw := foodDeficit_le_one w hw
  have hp := mul_le_mul (foodDeficit_resource u) (foodDeficit_resource w)
    (show 0 ≤ 1 - foodDeficit w by linarith) hu
  nlinarith [sq_nonneg (foodDeficit u+foodDeficit w-2/5),
    sq_nonneg (foodDeficit u-foodDeficit w)]

/-- Sharpened count-scale drift: constant `11/5` and logarithmic correction
`1500/(K-2)`. The physical adapter must supply `hlog`, the selected-birth and
adverse-copy-flux logarithmic bound with second-order terms `2uw/K` and
`(1+25C)/(K-2)`. -/
theorem count_log_occupation_sharp (u w du dw C K L V : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hC : 0 ≤ C) (hK : 2 < K)
    (huw : 4*(u*w) ≤ 121/4) (hdelta : 1+25*C ≤ 1476)
    (hdu : 1-u-23*C*u ≤ du) (hdw : 1-w-23*C*w ≤ dw)
    (hlog : 4*(u*w)-1-25*C-2*(u*w)/K-(1+25*C)/(K-2) ≤ L) :
    11/5-117*C-1500/(K-2)-768000/V ≤
      L+8*foodDeficit u*du+8*foodDeficit w*dw-768000/V := by
  have h1 := deficit_drift u du C hC hdu
  have h2 := deficit_drift w dw C hC hdw
  have hp := food_product_deficit_sharp u w hu hw
  have hk0 : 0 < K := by linarith
  have hk2 : 0 < K-2 := by linarith
  have hc1 : 2*(u*w)/K ≤ (121/8)/(K-2) := by
    apply (div_le_div_of_nonneg_right (show 2*(u*w) ≤ 121/8 by linarith) hk0.le).trans
    exact div_le_div_of_nonneg_left (by norm_num) hk2 (by linarith)
  have hc2 : (1+25*C)/(K-2) ≤ 1476/(K-2) :=
    div_le_div_of_nonneg_right hdelta hk2.le
  have hc3 : (121/8)/(K-2)+1476/(K-2) ≤ 1500/(K-2) := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) hk2.le
  linarith

/-- Weighted square bound with weights `101/100` and `101`; no independence. -/
theorem weighted_square (x y : ℝ) : (x+y)^2 ≤ (101/100)*x^2+101*y^2 := by
  nlinarith [sq_nonneg (x/10-10*y)]

/-- Potential range: `log (33/4 * 10^18) + 8 < 52`, in exponential form. -/
theorem potential_range_exp : (825 : ℝ)*10^16 < Real.exp 44 := by
  have he : Real.exp 44 = Real.exp 1 ^ 44 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h1 : (2.7182818283 : ℝ)^44 ≤ Real.exp 1 ^ 44 := by
    gcongr
    exact Real.exp_one_gt_d9.le
  rw [he]
  exact lt_of_lt_of_le (by norm_num) h1

/-- Scalar margins of the robust operating point `V = 2*10^22`, `h = 6667`,
`η = 10^-5`, `z = 48`, `d = 99`: Bernstein exponent above `24` and quota
above `1/10`. -/
theorem robust_operating_point_margins :
    let A : ℝ := 11/5-468/500000000-1287/100000-1500/6665-768000/(2*10^22)
    let q : ℝ := (101/100)*(121/6667+2952*6667/6665^2)+2482176000/(2*10^22)
    let b : ℝ := 2/6665+32/(2*10^22)
    (24 : ℝ) < 48^2/(2*(99*q+b*48/3)) ∧ (1/10 : ℝ) < (99*A-52-48)/624-1/20 := by
  norm_num

/-- The same point tolerates `η = 10^-4` with `z = 37` and exponent above `14`. -/
theorem robust_operating_point_margins_wide :
    let A : ℝ := 11/5-468/500000000-1287/10000-1500/6665-768000/(2*10^22)
    let q : ℝ := (101/100)*(121/6667+2952*6667/6665^2)+2482176000/(2*10^22)
    let b : ℝ := 2/6665+32/(2*10^22)
    (14 : ℝ) < 37^2/(2*(99*q+b*37/3)) ∧ (1/10 : ℝ) < (99*A-52-37)/624-1/20 := by
  norm_num

/-- Error budget at the robust operating point: two reward tails with
exponent `24`, nine clock tails with exponent `100`, and the dyadic floor
term with `N = 200`. -/
theorem robust_error_budget :
    2*Real.exp (-24)+9*Real.exp (-100)+3*10^8*201/2^200 < (1 : ℝ)/10^10 := by
  have hpow (n : ℕ) : (2.7182818283 : ℝ)^n ≤ Real.exp n := by
    have he : Real.exp n = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [he]
    gcongr
    exact Real.exp_one_gt_d9.le
  have h24 : Real.exp (-24) ≤ 1/(2.7182818283 : ℝ)^24 := by
    rw [Real.exp_neg, ← one_div]
    have h : (2.7182818283 : ℝ)^24 ≤ Real.exp 24 := by exact_mod_cast hpow 24
    exact one_div_le_one_div_of_le (by positivity) h
  have h48 : Real.exp (-48) ≤ 1/(2.7182818283 : ℝ)^48 := by
    rw [Real.exp_neg, ← one_div]
    have h : (2.7182818283 : ℝ)^48 ≤ Real.exp 48 := by exact_mod_cast hpow 48
    exact one_div_le_one_div_of_le (by positivity) h
  have h100 : Real.exp (-100) ≤ 1/(2.7182818283 : ℝ)^48 := by
    refine le_trans (Real.exp_le_exp.mpr (by norm_num)) h48
  have hnum : 2*(1/(2.7182818283 : ℝ)^24)+9*(1/(2.7182818283 : ℝ)^48)
      +3*10^8*201/2^200 < (1 : ℝ)/10^10 := by
    norm_num
  linarith

end StartupCount
