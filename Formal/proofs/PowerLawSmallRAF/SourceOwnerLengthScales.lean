import proofs.PowerLawSmallRAF.SourceLowBandScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

theorem nat_div_two_pow_tendsto_of_log_ratio (w : Nat → Nat)
    (hw : Tendsto w atTop atTop)
    (hl : Tendsto (fun n : Nat => Real.log (n : ℝ)/(w n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : Nat => (n : ℝ)/(2 : ℝ)^(w n)) atTop (𝓝 0) := by
  have ht := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp hw).atTop_mul_pos
    (by simpa using Real.log_pos (by norm_num : (1 : ℝ) < 2))
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2))).sub hl)
  have hn : Tendsto (fun n : Nat => -((w n : ℝ)*(Real.log 2-Real.log (n : ℝ)/(w n : ℝ))))
      atTop atBot := by
    rw [tendsto_atBot]
    intro B
    filter_upwards [ht.eventually_ge_atTop (-B)] with n hn
    dsimp only [Function.comp_apply] at hn
    linarith
  have he := Real.tendsto_exp_atBot.comp hn
  apply he.congr'
  filter_upwards [eventually_ge_atTop 1, hw.eventually (eventually_ge_atTop 1)] with n hn hw1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hwpos : (0 : ℝ) < w n := by exact_mod_cast (show 0 < w n by omega)
  have hid : -((w n : ℝ)*(Real.log 2-Real.log (n : ℝ)/(w n : ℝ))) =
      Real.log (n : ℝ)-(w n : ℝ)*Real.log 2 := by field_simp; ring
  simp only [Function.comp_apply]
  rw [hid, Real.exp_sub, Real.exp_log hnpos, ← Real.log_pow,
    Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)^(w n))]

theorem nat_div_two_pow_shrinking_tendsto_zero :
    Tendsto (fun n : Nat => (n : ℝ)/(2 : ℝ)^(shrinkingBandWidth n)) atTop (𝓝 0) := by
  apply nat_div_two_pow_tendsto_of_log_ratio shrinkingBandWidth shrinkingBandWidth_tendsto
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hp
  have hl := ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hl.div hf one_ne_zero
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 : (n : ℝ)^(3/4 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  change (Real.log (n : ℝ)/(n : ℝ)^(3/4 : ℝ))/
    ((shrinkingBandWidth n : ℝ)/(n : ℝ)^(3/4 : ℝ)) = Real.log (n : ℝ)/(shrinkingBandWidth n : ℝ)
  field_simp

theorem nat_div_two_pow_twohundredth_tendsto_zero :
    Tendsto (fun n : Nat => (n : ℝ)/(2 : ℝ)^(n/200)) atTop (𝓝 0) := by
  have hf : Tendsto (fun n : Nat => ((n/200 : Nat) : ℝ)/(n : ℝ)) atTop (𝓝 (1/200 : ℝ)) := by
    have h := (tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 1/200)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Function.comp_def, one_div, inv_mul_eq_div, Nat.floor_div_ofNat, Nat.floor_natCast] using h
  have hw : Tendsto (fun n : Nat => n/200) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (200*b)] with n hn
    omega
  apply nat_div_two_pow_tendsto_of_log_ratio (fun n => n/200) hw
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hl.div hf (by norm_num : (1/200 : ℝ) ≠ 0)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  change (Real.log (n : ℝ)/(n : ℝ))/(((n/200 : Nat) : ℝ)/(n : ℝ)) =
    Real.log (n : ℝ)/((n/200 : Nat) : ℝ)
  field_simp

end
end PowerLawSmallRAF
