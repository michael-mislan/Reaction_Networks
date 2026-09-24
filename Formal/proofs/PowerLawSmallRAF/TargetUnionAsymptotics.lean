import proofs.PowerLawSmallRAF.SourceOwnerLengthScales
import Mathlib.Analysis.Complex.ExponentialBounds

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def targetGrowth (n : Nat) : ℝ := (n : ℝ)^(3/4 : ℝ)
def targetNucleusLength (n : Nat) : Nat := ⌈8*(n : ℝ)^(1/2 : ℝ)⌉₊
def targetIntensity (n : Nat) : ℝ := (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ))
def highTargetLogCount (n : Nat) : ℝ := 3*Real.log (n : ℝ)+(shrinkingBandWidth n : ℝ)*Real.log 2
def lowTargetLogCount (n : Nat) : ℝ := ((targetNucleusLength n : ℝ)+1)*Real.log 2

theorem targetGrowth_tendsto : Tendsto targetGrowth atTop atTop :=
  (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<3/4)).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem targetGrowth_log_ratio :
    Tendsto (fun n : Nat => Real.log (n : ℝ)/targetGrowth n) atTop (𝓝 0) :=
  ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ)<3/4)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))

theorem targetNucleusLength_ratio :
    Tendsto (fun n : Nat => (targetNucleusLength n : ℝ)/(n : ℝ)^(1/2 : ℝ)) atTop (𝓝 8) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := (tendsto_nat_ceil_div_atTop (R := ℝ)).comp
    (hp.const_mul_atTop (by norm_num : (0 : ℝ)<8))
  have h := hc.const_mul 8
  simp only [mul_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  change 8*((targetNucleusLength n : ℝ)/(8*(n : ℝ)^(1/2 : ℝ))) = _
  field_simp

theorem targetNucleusLength_growth_ratio :
    Tendsto (fun n : Nat => (targetNucleusLength n : ℝ)/targetGrowth n) atTop (𝓝 0) := by
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := targetNucleusLength_ratio.mul hsmall
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n : ℝ)^(-(1/4 : ℝ)) = (n : ℝ)^(1/2 : ℝ)/targetGrowth n := by
    rw [targetGrowth,← Real.rpow_sub hn0]
    norm_num
  simp only [Function.comp_apply]
  rw [he]
  field_simp

theorem highTargetLogCount_ratio :
    Tendsto (fun n => highTargetLogCount n/targetGrowth n) atTop (𝓝 (Real.log 2)) := by
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp targetGrowth_tendsto
  have h := (targetGrowth_log_ratio.const_mul 3).add (hf.mul_const (Real.log 2))
  simp only [mul_zero,one_mul,zero_add] at h
  convert h using 1
  funext n
  change (3*Real.log (n : ℝ)+(shrinkingBandWidth n : ℝ)*Real.log 2)/targetGrowth n =
    3*(Real.log (n : ℝ)/targetGrowth n)+((shrinkingBandWidth n : ℝ)/targetGrowth n)*Real.log 2
  ring

theorem lowTargetLogCount_ratio :
    Tendsto (fun n => lowTargetLogCount n/targetGrowth n) atTop (𝓝 0) := by
  have hi : Tendsto (fun n => (1 : ℝ)/targetGrowth n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop targetGrowth_tendsto
  have h := (targetNucleusLength_growth_ratio.add hi).mul_const (Real.log 2)
  simp only [zero_add,zero_mul] at h
  convert h using 1
  funext n
  unfold lowTargetLogCount
  ring

theorem targetIntensity_scaled (n : Nat) (hn : 0<n) (x : ℝ) :
    targetIntensity n*x/targetGrowth n = (29/20 : ℝ)*(x/(n : ℝ)) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have he : (n : ℝ)^(-(1/4 : ℝ)) = targetGrowth n/(n : ℝ) := by
    change (n : ℝ)^(-(1/4 : ℝ)) = (n : ℝ)^(3/4 : ℝ)/(n : ℝ)
    rw [show -(1/4 : ℝ) = (3/4 : ℝ)-1 by norm_num,Real.rpow_sub hn0,Real.rpow_one]
  unfold targetIntensity
  rw [he]
  have hw : targetGrowth n ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
  field_simp

theorem targetNucleus_square_ratio :
    Tendsto (fun n => (targetNucleusLength n : ℝ)^2/(n : ℝ)) atTop (𝓝 64) := by
  have h := targetNucleusLength_ratio.pow 2
  norm_num at h ⊢
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs : ((n : ℝ)^(1/2 : ℝ))^2 = (n : ℝ) := by
    rw [pow_two,← Real.rpow_add hn0]
    norm_num
  rw [div_pow,hs]

theorem highTargetLength_ratio :
    Tendsto (fun n : Nat => ((n-2*shrinkingBandWidth n : Nat) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
    (shrinkingBandWidth_relative_tendsto.const_mul 2)
  simp only [mul_zero,sub_zero] at h
  apply h.congr'
  have hsmall := shrinkingBandWidth_relative_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))
  filter_upwards [eventually_ge_atTop 1,hsmall] with n hn hh
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hs : 2*shrinkingBandWidth n ≤ n := by
    have he := (div_lt_iff₀ hn0).mp hh
    have hh' : (2 : ℝ)*(shrinkingBandWidth n : ℝ) ≤ n := by linarith
    exact_mod_cast hh'
  rw [Nat.cast_sub hs,Nat.cast_mul,Nat.cast_ofNat]
  field_simp

theorem lowTargetLength_ratio :
    Tendsto (fun n : Nat => ((n/200 : Nat) : ℝ)/(n : ℝ)) atTop (𝓝 (1/200 : ℝ)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ)≤1/200)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def,one_div,inv_mul_eq_div,Nat.floor_div_ofNat,Nat.floor_natCast] using h

theorem target_exp_of_negative_ratio (f : Nat → ℝ) {c : ℝ} (hc : c<0)
    (hf : Tendsto (fun n => f n/targetGrowth n) atTop (𝓝 c)) :
    Tendsto (fun n => Real.exp (f n)) atTop (𝓝 0) := by
  have ht := targetGrowth_tendsto.atTop_mul_neg hc hf
  have he := Real.tendsto_exp_atBot.comp ht
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hw : targetGrowth n ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hn0 _)
  simp only [Function.comp_apply,mul_div_cancel₀ _ hw]

def targetDirectLog (K : Nat → ℝ) (m : Nat → Nat) (n : Nat) : ℝ :=
  K n-targetIntensity n*(m n : ℝ)/2
def targetDensityLog (K : Nat → ℝ) (n : Nat) : ℝ :=
  K n+Real.log 2+2*Real.log (n : ℝ)-targetIntensity n*(targetNucleusLength n : ℝ)^2/32

theorem targetDirectLog_ratio (K : Nat → ℝ) (m : Nat → Nat) {a b : ℝ}
    (hK : Tendsto (fun n => K n/targetGrowth n) atTop (𝓝 a))
    (hm : Tendsto (fun n => (m n : ℝ)/(n : ℝ)) atTop (𝓝 b)) :
    Tendsto (fun n => targetDirectLog K m n/targetGrowth n) atTop (𝓝 (a-(29/40 : ℝ)*b)) := by
  have h := hK.sub (hm.const_mul (29/40 : ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold targetDirectLog
  have he := targetIntensity_scaled n (by omega) (m n : ℝ)
  rw [sub_div]
  linear_combination he / 2

theorem targetDensityLog_ratio (K : Nat → ℝ) {a : ℝ}
    (hK : Tendsto (fun n => K n/targetGrowth n) atTop (𝓝 a)) :
    Tendsto (fun n => targetDensityLog K n/targetGrowth n) atTop (𝓝 (a-29/10)) := by
  have hi : Tendsto (fun n => Real.log 2/targetGrowth n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop targetGrowth_tendsto
  have h := ((hK.add hi).add (targetGrowth_log_ratio.const_mul 2)).sub
    (targetNucleus_square_ratio.const_mul (29/640 : ℝ))
  norm_num at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  unfold targetDensityLog
  have he := targetIntensity_scaled n (by omega) ((targetNucleusLength n : ℝ)^2)
  rw [sub_div,add_div,add_div]
  linear_combination he / 32

theorem high_target_error_logs_tendsto_zero :
    Tendsto (fun n => Real.exp (targetDirectLog highTargetLogCount
      (fun j => j-2*shrinkingBandWidth j) n)+Real.exp (targetDensityLog highTargetLogCount n))
      atTop (𝓝 0) := by
  have h1 := target_exp_of_negative_ratio _ (by linarith [Real.log_two_lt_d9] : Real.log 2-(29/40 : ℝ)*1<0)
    (targetDirectLog_ratio _ _ highTargetLogCount_ratio highTargetLength_ratio)
  have h2 := target_exp_of_negative_ratio _ (by linarith [Real.log_two_lt_d9] : Real.log 2-(29/10 : ℝ)<0)
    (targetDensityLog_ratio _ highTargetLogCount_ratio)
  simpa only [add_zero] using h1.add h2

theorem low_target_error_logs_tendsto_zero :
    Tendsto (fun n => Real.exp (targetDirectLog lowTargetLogCount (fun j => j/200) n)+
      Real.exp (targetDensityLog lowTargetLogCount n)) atTop (𝓝 0) := by
  have h1 := target_exp_of_negative_ratio _ (by norm_num : (0 : ℝ)-(29/40)*(1/200)<0)
    (targetDirectLog_ratio _ _ lowTargetLogCount_ratio lowTargetLength_ratio)
  have h2 := target_exp_of_negative_ratio _ (by norm_num : (0 : ℝ)-29/10<0)
    (targetDensityLog_ratio _ lowTargetLogCount_ratio)
  simpa only [add_zero] using h1.add h2

def targetUnionEnvelope (K : Nat → ℝ) (m : Nat → Nat) (n : Nat) : ℝ :=
  Real.exp (K n)*(Real.exp (-targetIntensity n*(m n : ℝ)/2)+
    2*(n : ℝ)^2*Real.exp (-targetIntensity n*(targetNucleusLength n : ℝ)^2/32))

theorem targetUnionEnvelope_eq_logs (K : Nat → ℝ) (m : Nat → Nat) (n : Nat) (hn : 0<n) :
    targetUnionEnvelope K m n = Real.exp (targetDirectLog K m n)+Real.exp (targetDensityLog K n) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hp : Real.exp (2*Real.log (n : ℝ)) = (n : ℝ)^2 := by
    rw [show 2*Real.log (n : ℝ) = Real.log (n : ℝ)+Real.log (n : ℝ) by ring,
      Real.exp_add,Real.exp_log hn0]
    ring
  unfold targetUnionEnvelope targetDirectLog targetDensityLog
  rw [Real.exp_sub,Real.exp_sub,Real.exp_add,Real.exp_add,hp,Real.exp_log (by norm_num : (0 : ℝ)<2)]
  simp only [neg_mul,neg_div,Real.exp_neg]
  ring

def highTargetError (n : Nat) : ℝ :=
  (n : ℝ)^3*(2 : ℝ)^(shrinkingBandWidth n)*
    (Real.exp (-targetIntensity n*((n-2*shrinkingBandWidth n : Nat) : ℝ)/2)+
      2*(n : ℝ)^2*Real.exp (-targetIntensity n*(targetNucleusLength n : ℝ)^2/32))

def lowTargetError (n : Nat) : ℝ :=
  (2 : ℝ)^(targetNucleusLength n+1)*
    (Real.exp (-targetIntensity n*((n/200 : Nat) : ℝ)/2)+
      2*(n : ℝ)^2*Real.exp (-targetIntensity n*(targetNucleusLength n : ℝ)^2/32))

theorem highTargetError_tendsto_zero : Tendsto highTargetError atTop (𝓝 0) := by
  apply high_target_error_logs_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← targetUnionEnvelope_eq_logs _ _ n (by omega)]
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h3 := Real.exp_log (pow_pos hn0 3)
  rw [Real.log_pow] at h3
  norm_num at h3
  have h2 := Real.exp_log (pow_pos (by norm_num : (0 : ℝ)<2) (shrinkingBandWidth n))
  rw [Real.log_pow] at h2
  unfold targetUnionEnvelope highTargetLogCount highTargetError
  rw [Real.exp_add,h3,h2]

theorem lowTargetError_tendsto_zero : Tendsto lowTargetError atTop (𝓝 0) := by
  apply low_target_error_logs_tendsto_zero.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← targetUnionEnvelope_eq_logs _ _ n (by omega)]
  have h2 := Real.exp_log (pow_pos (by norm_num : (0 : ℝ)<2) (targetNucleusLength n+1))
  rw [Real.log_pow] at h2
  unfold targetUnionEnvelope lowTargetLogCount lowTargetError
  rw [show ((targetNucleusLength n : ℝ)+1)*Real.log 2 =
    ((targetNucleusLength n+1 : Nat) : ℝ)*Real.log 2 by push_cast; rfl,h2]

end
end PowerLawSmallRAF
