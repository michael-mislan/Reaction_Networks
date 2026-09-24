import proofs.PowerLawSmallRAF.TargetUnionAsymptotics

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

theorem targetNucleusLength_relative_tendsto :
    Tendsto (fun n : Nat => (targetNucleusLength n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/2)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := targetNucleusLength_ratio.mul hsmall
  simp only [mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n : ℝ)^(-(1/2 : ℝ)) = (n : ℝ)^(1/2 : ℝ)/(n : ℝ) := by
    rw [show -(1/2 : ℝ) = (1/2 : ℝ)-1 by norm_num,Real.rpow_sub hn0,Real.rpow_one]
  simp only [Function.comp_apply]
  rw [he]
  field_simp

theorem targetIntensity_mul_nucleus_tendsto :
    Tendsto (fun n => targetIntensity n*(targetNucleusLength n : ℝ)) atTop atTop := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hp.atTop_mul_pos (by norm_num : (0 : ℝ)<(29/20)*8)
    (targetNucleusLength_ratio.const_mul (29/20 : ℝ))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n : ℝ)^(1/4 : ℝ) = (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) := by
    rw [← Real.rpow_add hn0]
    norm_num
  simp only [Function.comp_apply]
  rw [he,targetIntensity]
  field_simp

/-- All finite target-theorem hypotheses hold for the actual rounded scales. -/
theorem targetUnion_eventual_conditions :
    ∀ᶠ n : Nat in atTop, 0 ≤ targetIntensity n ∧ targetIntensity n ≤ 1 ∧
      4 ≤ targetNucleusLength n ∧ targetNucleusLength n ≤ n/200 ∧
      targetNucleusLength n ≤ n-2*shrinkingBandWidth n ∧
      32*Real.log 2 ≤ targetIntensity n*(targetNucleusLength n : ℝ) := by
  have hp0 : Tendsto targetIntensity atTop (𝓝 0) := by
    have h := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<1/4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul (29/20 : ℝ)
    simpa only [mul_zero] using h
  have hLtop : Tendsto targetNucleusLength atTop atTop :=
    tendsto_nat_ceil_atTop.comp
      (((tendsto_rpow_atTop (by norm_num : (0 : ℝ)<1/2)).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop (by norm_num : (0 : ℝ)<8))
  have hp := hp0 (Iic_mem_nhds (by norm_num : (0 : ℝ)<1))
  have hL := targetNucleusLength_relative_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/400))
  have hlo := lowTargetLength_ratio (Ioi_mem_nhds (by norm_num : (1/400 : ℝ)<1/200))
  have hhi := highTargetLength_ratio (Ioi_mem_nhds (by norm_num : (1/2 : ℝ)<1))
  filter_upwards [eventually_ge_atTop 1,hp,hL,hlo,hhi,hLtop.eventually_ge_atTop 4,
    targetIntensity_mul_nucleus_tendsto.eventually_ge_atTop (32*Real.log 2)] with n hn hp hL hlo hhi h4 hlarge
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (show 0<n by omega)
  change (targetNucleusLength n : ℝ)/(n : ℝ) < 1/400 at hL
  change (1/2 : ℝ) < ((n-2*shrinkingBandWidth n : Nat) : ℝ)/(n : ℝ) at hhi
  refine ⟨by unfold targetIntensity; positivity,hp,h4,?_,?_,hlarge⟩
  · have hlt := (div_lt_div_iff_of_pos_right hn0).mp (hL.trans hlo)
    exact_mod_cast hlt.le
  · have hlt : (targetNucleusLength n : ℝ)/(n : ℝ) <
        ((n-2*shrinkingBandWidth n : Nat) : ℝ)/(n : ℝ) := by linarith
    exact_mod_cast ((div_lt_div_iff_of_pos_right hn0).mp hlt).le

end
end PowerLawSmallRAF
