import proofs.ProductiveMemory.ExtractionSource
import proofs.FiniteCopy.LocalSourceBounds
import proofs.FiniteCopy.LocalExponentialRate

namespace ProductiveMemory
open FiniteCopy
noncomputable section
set_option Elab.async false

theorem low_channel_energy (c : ExtractionChannel) :
    0 ≤ lowExtractionEnergy (channelJump c) ∧ lowExtractionEnergy (channelJump c) ≤ 210 := by
  cases c with
  | inl r => fin_cases r <;> norm_num [lowExtractionEnergy,lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
  | inr r => norm_num [lowExtractionEnergy,lowExtractionPair,channelJump,Matrix.cons_val_two,Matrix.cons_val_three]

theorem low_channel_pair_sq (y : Point) (c : ExtractionChannel) :
    (2*lowExtractionPair y (channelJump c))^2 ≤ 100000*normSq y := by
  cases c with
  | inl r =>
    fin_cases r
    · have h := linear_four_sq (36239/31250:ℝ) (-56819/50000:ℝ) (392409/100000:ℝ) (3119749/500000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-36239/31250:ℝ) (56819/50000:ℝ) (-392409/100000:ℝ) (-3119749/500000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (1038971/500000:ℝ) (-255193/125000:ℝ) (3217447/500000:ℝ) (5049887/500000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-1038971/500000:ℝ) (255193/125000:ℝ) (-3217447/500000:ℝ) (-5049887/500000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (297097/125000:ℝ) (-73351/31250:ℝ) (633269/100000:ℝ) (568919/62500:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-297097/125000:ℝ) (73351/31250:ℝ) (-633269/100000:ℝ) (-568919/62500:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (539561/250000:ℝ) (-568413/500000:ℝ) (2227359/500000:ℝ) (326633/50000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-539561/250000:ℝ) (568413/500000:ℝ) (-2227359/500000:ℝ) (-326633/50000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-568413/500000:ℝ) (211557/100000:ℝ) (-548597/125000:ℝ) (-80379/12500:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (568413/500000:ℝ) (-211557/100000:ℝ) (548597/125000:ℝ) (80379/12500:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (2726657/500000:ℝ) (-2194611/500000:ℝ) (3324553/250000:ℝ) (487391/25000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-2726657/500000:ℝ) (2194611/500000:ℝ) (-3324553/250000:ℝ) (-487391/25000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-326633/50000:ℝ) (80379/12500:ℝ) (-9601239/500000:ℝ) (-7325563/250000:ℝ) y
      norm_num only at h
      norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
  | inr r =>
    have h := linear_four_sq (-2227359/500000:ℝ) (548597/125000:ℝ) (-398987/31250:ℝ) (-9601239/500000:ℝ) y
    norm_num only at h
    norm_num [lowExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg y]

theorem low_extraction_energy_add (y v : Point) :
    lowExtractionEnergy (fun i => y i+v i) = lowExtractionEnergy y+2*lowExtractionPair y v+lowExtractionEnergy v := by
  unfold lowExtractionEnergy lowExtractionPair
  ring

theorem low_pair_drift (rho q : ℝ) (y x : Point) :
    (∑ c : ExtractionChannel, channelDensity rho q x c*(2*lowExtractionPair y (channelJump c))) =
      2*lowExtractionPair y (extractDrift rho q x) := by
  norm_num [lowExtractionPair,extractDrift,drift_formula,channelDensity,channelJump,densityRates,jump,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem low_pair_correction (rho q : ℝ) (y x : Point) :
    2*lowExtractionPair y (extractDrift rho q x) = 2*lowExtractionPair y (extractDrift rho 0 x)+
      q*(2*lowExtractionPair y (sourceCorrection x)) := by
  norm_num [lowExtractionPair,extractDrift,drift_formula,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem low_correction_bound (y x : Point) (hy : ∀ i, |y i| ≤ 1/400)
    (hx : ∀ i, |x i| ≤ 35) : 2*lowExtractionPair y (sourceCorrection x) ≤ 10000 := by
  have t00 := bounded_bilinear_term (y 0) (x 0) (2726657/50000000000:ℝ) (hy 0) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t00
  have t01 := bounded_bilinear_term (y 0) (x 2) (297097/62500:ℝ) (hy 0) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t01
  have t10 := bounded_bilinear_term (y 1) (x 0) (-2194611/50000000000:ℝ) (hy 1) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have t11 := bounded_bilinear_term (y 1) (x 2) (-73351/15625:ℝ) (hy 1) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t11
  have t20 := bounded_bilinear_term (y 2) (x 0) (3324553/25000000000:ℝ) (hy 2) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t20
  have t21 := bounded_bilinear_term (y 2) (x 2) (633269/50000:ℝ) (hy 2) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t21
  have t30 := bounded_bilinear_term (y 3) (x 0) (487391/2500000000:ℝ) (hy 3) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t30
  have t31 := bounded_bilinear_term (y 3) (x 2) (568919/31250:ℝ) (hy 3) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t31
  norm_num [lowExtractionPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  nlinarith only [t00,t01,t10,t11,t20,t21,t30,t31]

theorem high_channel_energy (c : ExtractionChannel) :
    0 ≤ highExtractionEnergy (channelJump c) ∧ highExtractionEnergy (channelJump c) ≤ 210 := by
  cases c with
  | inl r => fin_cases r <;> norm_num [highExtractionEnergy,highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
  | inr r => norm_num [highExtractionEnergy,highExtractionPair,channelJump,Matrix.cons_val_two,Matrix.cons_val_three]

theorem high_channel_pair_sq (y : Point) (c : ExtractionChannel) :
    (2*highExtractionPair y (channelJump c))^2 ≤ 100000*normSq y := by
  cases c with
  | inl r =>
    fin_cases r
    · have h := linear_four_sq (477627/500000:ℝ) (-1624651/500000:ℝ) (1431227/250000:ℝ) (2189577/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-477627/500000:ℝ) (1624651/500000:ℝ) (-1431227/250000:ℝ) (-2189577/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (1456619/500000:ℝ) (-2109157/250000:ℝ) (7191633/500000:ℝ) (2182637/100000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-1456619/500000:ℝ) (2109157/250000:ℝ) (-7191633/500000:ℝ) (-2182637/100000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (74901/25000:ℝ) (-2051277/250000:ℝ) (868291/62500:ℝ) (10416409/500000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-74901/25000:ℝ) (2051277/250000:ℝ) (-868291/62500:ℝ) (-10416409/500000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (244049/125000:ℝ) (-93801/31250:ℝ) (2954639/500000:ℝ) (2205629/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-244049/125000:ℝ) (93801/31250:ℝ) (-2954639/500000:ℝ) (-2205629/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-93801/31250:ℝ) (5195401/500000:ℝ) (-2080217/125000:ℝ) (-6269591/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (93801/31250:ℝ) (-5195401/500000:ℝ) (2080217/125000:ℝ) (6269591/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (431651/62500:ℝ) (-8197033/500000:ℝ) (7115073/250000:ℝ) (10680849/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-431651/62500:ℝ) (8197033/500000:ℝ) (-7115073/250000:ℝ) (-10680849/250000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
    · have h := linear_four_sq (-2205629/250000:ℝ) (6269591/250000:ℝ) (-10664797/250000:ℝ) (-32242779/500000:ℝ) y
      norm_num only at h
      norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
      nlinarith only [h,normSq_nonneg y]
  | inr r =>
    have h := linear_four_sq (-2954639/500000:ℝ) (2080217/125000:ℝ) (-14137961/500000:ℝ) (-10664797/250000:ℝ) y
    norm_num only at h
    norm_num [highExtractionPair,channelJump,jump,Matrix.cons_val_two,Matrix.cons_val_three]
    nlinarith only [h,normSq_nonneg y]

theorem high_extraction_energy_add (y v : Point) :
    highExtractionEnergy (fun i => y i+v i) = highExtractionEnergy y+2*highExtractionPair y v+highExtractionEnergy v := by
  unfold highExtractionEnergy highExtractionPair
  ring

theorem high_pair_drift (rho q : ℝ) (y x : Point) :
    (∑ c : ExtractionChannel, channelDensity rho q x c*(2*highExtractionPair y (channelJump c))) =
      2*highExtractionPair y (extractDrift rho q x) := by
  norm_num [highExtractionPair,extractDrift,drift_formula,channelDensity,channelJump,densityRates,jump,
    Fintype.sum_sum_type,Fin.sum_univ_succ,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem high_pair_correction (rho q : ℝ) (y x : Point) :
    2*highExtractionPair y (extractDrift rho q x) = 2*highExtractionPair y (extractDrift rho 0 x)+
      q*(2*highExtractionPair y (sourceCorrection x)) := by
  norm_num [highExtractionPair,extractDrift,drift_formula,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  ring

theorem high_correction_bound (y x : Point) (hy : ∀ i, |y i| ≤ 1/400)
    (hx : ∀ i, |x i| ≤ 35) : 2*highExtractionPair y (sourceCorrection x) ≤ 10000 := by
  have t00 := bounded_bilinear_term (y 0) (x 0) (431651/6250000000:ℝ) (hy 0) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t00
  have t01 := bounded_bilinear_term (y 0) (x 2) (74901/12500:ℝ) (hy 0) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t01
  have t10 := bounded_bilinear_term (y 1) (x 0) (-8197033/50000000000:ℝ) (hy 1) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t10
  have t11 := bounded_bilinear_term (y 1) (x 2) (-2051277/125000:ℝ) (hy 1) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t11
  have t20 := bounded_bilinear_term (y 2) (x 0) (7115073/25000000000:ℝ) (hy 2) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t20
  have t21 := bounded_bilinear_term (y 2) (x 2) (868291/31250:ℝ) (hy 2) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t21
  have t30 := bounded_bilinear_term (y 3) (x 0) (10680849/25000000000:ℝ) (hy 3) (hx 0)
  norm_num only [abs_of_pos,abs_of_neg] at t30
  have t31 := bounded_bilinear_term (y 3) (x 2) (10416409/250000:ℝ) (hy 3) (hx 2)
  norm_num only [abs_of_pos,abs_of_neg] at t31
  norm_num [highExtractionPair,sourceCorrection,Matrix.cons_val_two,Matrix.cons_val_three]
  nlinarith only [t00,t01,t10,t11,t20,t21,t30,t31]

theorem extraction_exponential_rate_bound {ι : Type*} [Fintype ι] (a L Q : ι → ℝ) (q v : ℝ)
    (ha : ∀ r, 0 ≤ a r) (hsum : ∑ r, a r ≤ 200000)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 ≤ v) (hv1 : v ≤ 1/40000)
    (hL : ∀ r, (L r)^2 ≤ 100000*v)
    (hQ : ∀ r, 0 ≤ Q r ∧ Q r ≤ 210)
    (hdrift : ∑ r, a r*L r ≤ -(59/100)*v+10000*q) :
    ∑ r, a r*(Real.exp (localAlpha*(L r+q*Q r))-1) ≤
      localAlpha*(-(1/2)*v+100000000*q) := by
  let c := localAlpha*q*210+2*localAlpha^2*100000*v+2*localAlpha^2*q^2*44100
  have hc : 0 ≤ c := by dsimp [c,localAlpha]; positivity
  have hpoint (r) : a r*(Real.exp (localAlpha*(L r+q*Q r))-1) ≤
      localAlpha*(a r*L r)+a r*c := by
    have h := mul_le_mul_of_nonneg_left
      (local_exponential_increment_bound (L r) (Q r) q v hq hq1 hv1 (hL r) (hQ r).1 (hQ r).2) (ha r)
    dsimp [c]
    nlinarith only [h]
  have hsum1 := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hpoint r)
  have hid : (∑ r, (localAlpha*(a r*L r)+a r*c)) =
      localAlpha*(∑ r, a r*L r)+(∑ r, a r)*c := by
    rw [Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
  rw [hid] at hsum1
  have hd := mul_le_mul_of_nonneg_left hdrift (by norm_num [localAlpha] : 0 ≤ localAlpha)
  have hh := mul_le_mul_of_nonneg_right hsum hc
  have hq2 : q^2 ≤ q := by nlinarith
  dsimp [c,localAlpha] at hsum1 hd hh ⊢
  nlinarith only [hsum1,hd,hh,hq2,hq,hv]


end
end ProductiveMemory
