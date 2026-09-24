import proofs.FiniteCopy.WellExit

namespace FiniteCopy
open CoreCouplingCAC Set

noncomputable def markAB : Fin 13 → ℝ := ![1,-1,0,0,0,0,0,0,0,0,-1,1,0]
noncomputable def markZH : Fin 13 → ℝ := ![0,0,-1,1,2,-2,0,0,0,0,0,0,0]
noncomputable def markH : Fin 13 → ℝ := ![0,0,1,-1,-1,1,0,0,0,0,0,0,0]
noncomputable def markSink : Fin 13 → ℝ := ![0,0,0,0,0,0,0,0,0,0,0,0,1]

theorem H_stock_channel_identity (r : Fin 13) : markH r = jump r 3+markSink r := by
  fin_cases r <;> norm_num [markH,jump,markSink,Matrix.cons_val_three]

theorem activity_AB_formula (x : Point) (q : ℝ) :
    (∑ r, densityRates (1/100000) q x r*markAB r) =
      x 0-x 1*x 2+((x 0)^2-x 1)/100000-q*x 0/100000 := by
  norm_num [densityRates,markAB,Fin.sum_univ_succ]
  ring

theorem activity_ZH_formula (x : Point) (q : ℝ) :
    (∑ r, densityRates (1/100000) q x r*markZH r) =
      -16*x 2+3*x 3-4*(x 2)^2+4*q*x 2 := by
  norm_num [densityRates,markZH,Fin.sum_univ_succ]
  ring

theorem markAB_square (r : Fin 13) : (markAB r)^2 ≤ 4 := by fin_cases r <;> norm_num [markAB]
theorem markZH_square (r : Fin 13) : (markZH r)^2 ≤ 4 := by fin_cases r <;> norm_num [markZH]

theorem activity_variance_bound (N : ℕ) (n : Counts) (mark : Fin 13 → ℝ)
    (hm : ∀ r, (mark r)^2 ≤ 4) (hx : ∀ i, concentration N n i ≤ 35) :
    ∑ r, densityRates (1/100000) (1/(N : ℝ)) (concentration N n) r*(mark r)^2 ≤ 1000000 := by
  have hn (r) := lattice_rates_nonneg (1/100000) (by norm_num) N n r
  have hsum := local_rate_sum_upper (concentration N n) (1/(N : ℝ)) (by positivity)
    (fun i => ⟨by unfold concentration; positivity,hx i⟩)
  have hh := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hm r) (hn r))
  rw [← Finset.sum_mul] at hh
  linarith only [hh,hsum]

theorem nearby_upper (x s : Point) (hs : ∀ i, s i ≤ 34) (hy : ∀ i, |x i-s i| ≤ 1/400) (i : Fin 4) : x i ≤ 35 := by
  have h := (abs_le.mp (hy i)).2
  linarith [hs i]

theorem lowactivity_margins (z : ℝ) (hz : z ∈ Icc (99579401232/100000000000 : ℝ) (99579401233/100000000000)) (x : Point) (q : ℝ) (hq : 0 ≤ q)
    (hy : ∀ i, |x i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    (∑ r, densityRates (1/100000) q x r*markAB r) ≤ -2 ∧
    2 ≤ (∑ r, densityRates (1/100000) q x r*markZH r) ∧
    7/10000 ≤ densityRates (1/100000) q x 12 := by
  have hb := low_source_box z hz
  have h0 := abs_le.mp (hy 0)
  have h1 := abs_le.mp (hy 1)
  have h2 := abs_le.mp (hy 2)
  have h3 := abs_le.mp (hy 3)
  norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three] at h0 h1 h2 h3
  have ha0 : 0 ≤ x 0 := by linarith [h0.1,hb.1.1]
  have ha : x 0 ≤ 15 := by linarith [h0.2,hb.1.2]
  have hB : 20 ≤ x 1 := by linarith [h1.1,hb.2.1.1]
  have hzl : 99/100 ≤ x 2 := by linarith [h2.1,hz.1]
  have hzh : x 2 ≤ 101/100 := by linarith [h2.2,hz.2]
  have hH : 79/10 ≤ x 3 := by linarith [h3.1,hb.2.2.1]
  have ha2 : (x 0)^2 ≤ 15^2 := by nlinarith only [ha0,ha]
  have hz2 : (x 2)^2 ≤ (101/100)^2 := by nlinarith only [hzl,hzh]
  have hprod : (20:ℝ)*(99/100) ≤ x 1*x 2 := by
    exact mul_le_mul hB hzl (by norm_num) (by linarith only [hB])
  have hqa := mul_nonneg hq ha0
  have hqz := mul_nonneg hq (by linarith only [hzl] : 0 ≤ x 2)
  rw [activity_AB_formula,activity_ZH_formula]
  norm_num [densityRates]
  constructor
  · nlinarith only [ha,hB,ha2,hprod,hqa]
  constructor
  · nlinarith only [hzh,hH,hz2,hqz]
  · change 7/10000 ≤ x 3/10000
    linarith only [hH]

theorem highactivity_margins (z : ℝ) (hz : z ∈ Icc (297636724376/100000000000 : ℝ) (297636724377/100000000000)) (x : Point) (q : ℝ) (hq : 0 ≤ q)
    (hy : ∀ i, |x i-pointOfState (lift sourceRates z) i| ≤ 1/400) :
    (∑ r, densityRates (1/100000) q x r*markAB r) ≤ -2 ∧
    2 ≤ (∑ r, densityRates (1/100000) q x r*markZH r) ∧
    7/10000 ≤ densityRates (1/100000) q x 12 := by
  have hb := high_source_box z hz
  have h0 := abs_le.mp (hy 0)
  have h1 := abs_le.mp (hy 1)
  have h2 := abs_le.mp (hy 2)
  have h3 := abs_le.mp (hy 3)
  norm_num [pointOfState,lift,Matrix.cons_val_two,Matrix.cons_val_three] at h0 h1 h2 h3
  have ha0 : 0 ≤ x 0 := by linarith [h0.1,hb.1.1]
  have ha : x 0 ≤ 23 := by linarith [h0.2,hb.1.2]
  have hB : 12 ≤ x 1 := by linarith [h1.1,hb.2.1.1]
  have hzl : 297/100 ≤ x 2 := by linarith [h2.1,hz.1]
  have hzh : x 2 ≤ 298/100 := by linarith [h2.2,hz.2]
  have hH : 319/10 ≤ x 3 := by linarith [h3.1,hb.2.2.1]
  have ha2 : (x 0)^2 ≤ 23^2 := by nlinarith only [ha0,ha]
  have hz2 : (x 2)^2 ≤ (298/100)^2 := by nlinarith only [hzl,hzh]
  have hprod : (12:ℝ)*(297/100) ≤ x 1*x 2 := by
    exact mul_le_mul hB hzl (by norm_num) (by linarith only [hB])
  have hqa := mul_nonneg hq ha0
  have hqz := mul_nonneg hq (by linarith only [hzl] : 0 ≤ x 2)
  rw [activity_AB_formula,activity_ZH_formula]
  norm_num [densityRates]
  constructor
  · nlinarith only [ha,hB,ha2,hprod,hqa]
  constructor
  · nlinarith only [hzh,hH,hz2,hqz]
  · change 7/10000 ≤ x 3/10000
    linarith only [hH]

end FiniteCopy
