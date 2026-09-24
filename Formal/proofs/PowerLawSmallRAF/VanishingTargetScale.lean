import proofs.PowerLawSmallRAF.VanishingLowOwnerLength
import proofs.PowerLawSmallRAF.TargetUnionConditions

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

theorem vanishingLowBandWidth_growth_ratio_tendsto_atTop :
    Tendsto (fun n => (vanishingLowBandWidth n : ℝ)/targetGrowth n) atTop atTop := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hp
  have hg := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hg.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) hf
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he : (n : ℝ)^(1/8 : ℝ) = (n : ℝ)^(7/8 : ℝ)/targetGrowth n := by
    rw [targetGrowth,← Real.rpow_sub hnpos]
    norm_num
  change (n : ℝ)^(1/8 : ℝ)*((vanishingLowBandWidth n : ℝ)/(n : ℝ)^(7/8 : ℝ)) = _
  rw [he]
  field_simp

theorem sourceVanishingLowOwnerLength_eventually_large :
    ∀ᶠ n : Nat in atTop, 16*targetGrowth n ≤ (sourceVanishingLowOwnerLength n : ℝ) := by
  filter_upwards [vanishingLowBandWidth_growth_ratio_tendsto_atTop.eventually_ge_atTop 17,
    eventually_ge_atTop 1] with n hb hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hg : 0 < targetGrowth n := Real.rpow_pos_of_pos hnpos _
  have hk := (le_div_iff₀ hg).mp hb
  have hh : (shrinkingBandWidth n : ℝ) ≤ targetGrowth n := Nat.floor_le hg.le
  rw [sourceVanishingLowOwnerLength,Nat.cast_sub (vanishingLowBandWidth_ge_shrinking n hn)]
  linarith

theorem sourceVanishingLowOwnerLength_eventually_nucleus :
    ∀ᶠ n : Nat in atTop, targetNucleusLength n ≤ sourceVanishingLowOwnerLength n := by
  have hL := targetNucleusLength_growth_ratio.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [sourceVanishingLowOwnerLength_eventually_large,hL,eventually_ge_atTop 1] with n hm hL hn
  have hg : 0 < targetGrowth n := Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < n by omega)) _
  have hLn := (div_lt_one hg).mp hL
  have hr : (targetNucleusLength n : ℝ) ≤ sourceVanishingLowOwnerLength n := by linarith
  exact_mod_cast hr

theorem targetIntensity_growth_product (n : Nat) (hn : 1 ≤ n) :
    targetIntensity n*targetGrowth n = (29/20 : ℝ)*(n : ℝ)^(1/2 : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  unfold targetIntensity targetGrowth
  rw [mul_assoc,← Real.rpow_add hnpos]
  norm_num

theorem vanishingTargetDirectLog_eventually_le :
    ∀ᶠ n : Nat in atTop,
      targetDirectLog lowTargetLogCount sourceVanishingLowOwnerLength n ≤ -(n : ℝ)^(1/2 : ℝ) := by
  have hL := targetNucleusLength_ratio.eventually (gt_mem_nhds (by norm_num : (8 : ℝ) < 9))
  filter_upwards [sourceVanishingLowOwnerLength_eventually_large,hL,eventually_ge_atTop 1] with n hm hL hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hs0 : 0 < (n : ℝ)^(1/2 : ℝ) := Real.rpow_pos_of_pos hnpos _
  have hs1 : 1 ≤ (n : ℝ)^(1/2 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
  have hLn := (div_lt_iff₀ hs0).mp hL
  have hlog : lowTargetLogCount n ≤ 10*(n : ℝ)^(1/2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9)
      (show (0 : ℝ) ≤ (targetNucleusLength n : ℝ)+1 by positivity)
    unfold lowTargetLogCount
    nlinarith
  have hp : 0 ≤ targetIntensity n := by unfold targetIntensity; positivity
  have hcost := mul_le_mul_of_nonneg_left hm (div_nonneg hp (by norm_num : (0 : ℝ) ≤ 2))
  have he := targetIntensity_growth_product n hn
  unfold targetDirectLog
  nlinarith

theorem vanishingTargetDirectExp_tendsto_zero :
    Tendsto (fun n => Real.exp (targetDirectLog lowTargetLogCount sourceVanishingLowOwnerLength n))
      atTop (𝓝 0) := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have he := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards with n
    exact (Real.exp_pos _).le
  · filter_upwards [vanishingTargetDirectLog_eventually_le] with n hn
    exact Real.exp_le_exp.mpr hn

end
end PowerLawSmallRAF
