import proofs.RandomViability.CollectiveGrowth

namespace RandomViability
set_option maxHeartbeats 100000

theorem shifted_deficit_bounds (u a η : ℝ) (hu : 0 ≤ u) (hη : 0 ≤ η) (ha : |a| ≤ η) :
    foodDeficit (u-a) ≤ 1+η ∧ foodDeficit u-foodDeficit (u-a) ≤ η := by
  have haL := (abs_le.mp ha).1
  have haU := (abs_le.mp ha).2
  have hd := foodDeficit_nonneg (u-a)
  have hh : 1-(u-a) ≤ foodDeficit (u-a) := le_max_left _ _
  constructor
  · exact max_le (by linarith only [hu,haU]) (by linarith only [hη])
  · have he : foodDeficit u ≤ foodDeficit (u-a)+η := by
      apply max_le
      · linarith only [hh,haL]
      · linarith only [hd,hη]
    linarith only [he]

theorem shifted_deficit_square (u a η : ℝ) (hu : 0 ≤ u)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) (ha : |a| ≤ η) :
    (foodDeficit u)^2 ≤ (foodDeficit (u-a))^2+3*η := by
  have hh := shifted_deficit_bounds u a η hu hη ha
  have hu0 := foodDeficit_nonneg u
  have hv0 := foodDeficit_nonneg (u-a)
  have hu1 := foodDeficit_le_one u hu
  have hp := mul_nonneg (sub_nonneg.mpr hh.2) (add_nonneg hu0 hv0)
  have hs : foodDeficit u+foodDeficit (u-a) ≤ 3 := by linarith only [hu1,hh.1,hη1]
  have hs' := mul_le_mul_of_nonneg_left hs hη
  nlinarith only [hp,hs']

theorem shifted_deficit_drift (u a du C η : ℝ)
    (hu : 0 ≤ u) (hC : 0 ≤ C) (hη : 0 ≤ η) (ha : |a| ≤ η)
    (hdu : 1-u-23*C*u ≤ du) :
    8*(foodDeficit (u-a))^2-46*C-8*(1+η)*η*(1+23*C) ≤
      8*foodDeficit (u-a)*du := by
  have hd : 1-(u-a)-23*C*(u-a) ≤ du+(1+23*C)*a := by nlinarith only [hdu]
  have hh := deficit_drift (u-a) (du+(1+23*C)*a) C hC hd
  have hv := (shifted_deficit_bounds u a η hu hη ha).1
  have hp : foodDeficit (u-a)*a ≤ (1+η)*η := by
    calc
      _ ≤ foodDeficit (u-a)*η := mul_le_mul_of_nonneg_left (abs_le.mp ha).2 (foodDeficit_nonneg _)
      _ ≤ (1+η)*η := mul_le_mul_of_nonneg_right hv hη
  have he := mul_le_mul_of_nonneg_left hp (show 0 ≤ 8*(1+23*C) by positivity)
  nlinarith only [hh,he]

theorem shifted_log_drift (u w x a dx C : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 < x) (hC : 0 ≤ C)
    (ha : |a| ≤ x/100) (hdx : x*(4*u*w-1-25*C) ≤ dx) :
    (99/100 : ℝ)*4*u*w-(51/50 : ℝ)*(1+25*C) ≤ dx/(x-a) := by
  have haL := (abs_le.mp ha).1
  have haU := (abs_le.mp ha).2
  have hy : 0 < x-a := by linarith only [hx,haU]
  have hl : (99/100 : ℝ) ≤ x/(x-a) := (le_div_iff₀ hy).mpr (by linarith only [hx,haL])
  have hr : x/(x-a) ≤ (51/50 : ℝ) := (div_le_iff₀ hy).mpr (by linarith only [hx,haU])
  have hd := div_le_div_of_nonneg_right hdx hy.le
  have hp := mul_le_mul_of_nonneg_right hl (show 0 ≤ 4*u*w by positivity)
  have hn := mul_le_mul_of_nonneg_right hr (show 0 ≤ 1+25*C by positivity)
  have he : x*(4*u*w-1-25*C)/(x-a) = (x/(x-a))*(4*u*w)-(x/(x-a))*(1+25*C) := by ring
  rw [he] at hd
  nlinarith only [hd,hp,hn]

/-- Robust corrected growth at continuous compensated coordinates. Current
startup tolerances suffice; the positive basal product gain may be discarded. -/
theorem compensated_collective_growth (u w x au aw ax du dw dx C : ℝ)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hx : 0 < x) (hC : 0 ≤ C)
    (hau : |au| ≤ (1/100000 : ℝ)) (haw : |aw| ≤ (1/100000 : ℝ))
    (hax : |ax| ≤ x/100)
    (hdu : 1-u-23*C*u ≤ du) (hdw : 1-w-23*C*w ≤ dw)
    (hdx : x*(4*u*w-1-25*C) ≤ dx) :
    (19/10 : ℝ)-120*C ≤ dx/(x-ax)-
      4*(-2*foodDeficit (u-au)*du-2*foodDeficit (w-aw)*dw) := by
  have hsU := shifted_deficit_square u au (1/100000) hu (by norm_num) (by norm_num) hau
  have hsW := shifted_deficit_square w aw (1/100000) hw (by norm_num) (by norm_num) haw
  have hdU := shifted_deficit_drift u au du C (1/100000) hu hC (by norm_num) hau hdu
  have hdW := shifted_deficit_drift w aw dw C (1/100000) hw hC (by norm_num) haw hdw
  have hlog := shifted_log_drift u w x ax dx C hu hw hx hC hax hdx
  have hprod := food_product_deficit u w hu hw
  have hcore : (297/100 : ℝ) ≤ (99/100 : ℝ)*4*u*w+
      8*(foodDeficit u)^2+8*(foodDeficit w)^2 := by
    nlinarith only [hprod,sq_nonneg (foodDeficit u),sq_nonneg (foodDeficit w)]
  nlinarith only [hsU,hsW,hdU,hdW,hlog,hcore,hC]

end RandomViability
