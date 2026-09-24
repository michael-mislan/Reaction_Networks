import proofs.PowerLawSmallRAF.SourceHighBandConcentration

namespace PowerLawSmallRAF
open RAF RAF.Polymer RAF.Concrete Filter Topology
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def sourceHighBandMeanIntensity (n : Nat) : ℝ :=
  (49/50 : ℝ)*(19/20 : ℝ)*((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceHighBandMean n

private theorem rational_le_coverage {x : ℝ} (hx : 0 ≤ x) :
    x/(1+x) ≤ 1-Real.exp (-x) := by
  have hb : 1+x ≤ Real.exp x := by linarith only [Real.add_one_le_exp x]
  have hm := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-x)).le
  have hid : Real.exp (-x)*Real.exp x = 1 := by rw [← Real.exp_add]; simp
  rw [hid] at hm
  apply (div_le_iff₀ (by linarith : 0 < 1+x)).mpr
  nlinarith only [hm]

theorem sourceHighBand_mean_coverage_budget :
    ∀ᶠ n : Nat in atTop, (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) ≤
      1-Real.exp (-sourceHighBandMeanIntensity n) := by
  have hmargin : (147/100 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
      (((19/5 : ℝ)*Real.log 2)/(Real.pi^2/6)) := by
    have hp : Real.pi^2 < (3.15 : ℝ)^2 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
    rw [← mul_div_assoc, lt_div_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9]
  have hlim := (tendsto_const_nhds : Tendsto (fun _ : Nat => (49/50 : ℝ)*(19/20 : ℝ))
    atTop (𝓝 ((49/50 : ℝ)*(19/20 : ℝ)))).mul sourceShrinkingBandDensity_tendsto
  have hc := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hlim (Ioi_mem_nhds hmargin),
    hc (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/200)), eventually_ge_atTop 1] with n hn hc hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let c := (n : ℝ)^(-(1/4 : ℝ))
  have hc0 : 0 < c := Real.rpow_pos_of_pos hnpos _
  change c < (1/200 : ℝ) at hc
  have ht : (147/100 : ℝ)*c ≤ sourceHighBandMeanIntensity n := by
    change (147/100 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
      ((n : ℝ)^(1/4 : ℝ)*((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceHighBandMean n) at hn
    dsimp [c, sourceHighBandMeanIntensity]
    rw [Real.rpow_neg hnpos.le, ← div_eq_mul_inv]
    apply (div_le_iff₀ (Real.rpow_pos_of_pos hnpos _)).mpr
    nlinarith only [hn.le]
  have hrat := rational_le_coverage (by positivity : 0 ≤ (147/100 : ℝ)*c)
  have hexp := Real.exp_le_exp.mpr (neg_le_neg ht)
  have hsmall : (29/20 : ℝ)*c ≤ ((147/100 : ℝ)*c)/(1+(147/100 : ℝ)*c) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hc0, hc]
  exact hsmall.trans (hrat.trans (by linarith only [hexp]))

def sourceHighBandCoverageFailureMass (n : Nat) : ℝ :=
  ∑ config : SourceMoleculeFibreConfig n,
    if 1-Real.exp (-((19/20 : ℝ)/(sourceReactionCount n : ℝ)*
        ∑ x : Molecule n, truncatedBandValue (sourceShrinkingLower n) (sourceShrinkingUpper n) (config x))) <
      (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ))
    then sourcePowerLawConfigWeight (2-2/(n : ℝ)) n config else 0

theorem sourceHighBandCoverageFailureMass_tendsto_zero :
    Tendsto sourceHighBandCoverageFailureMass atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds sourceHighBandDeficitMass_tendsto_zero
  · filter_upwards [eventually_ge_atTop 4] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    apply Finset.sum_nonneg
    intro config _
    split_ifs
    · exact sourcePowerLawConfigWeight_nonneg _ _ ha config
    · exact le_rfl
  · filter_upwards [sourceHighBand_mean_coverage_budget, eventually_ge_atTop 4] with n hb hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    have hR : (0 : ℝ) < sourceReactionCount n := by
      exact_mod_cast (show 0 < sourceReactionCount n by simp [sourceReactionCount])
    apply Finset.sum_le_sum
    intro config _
    have hw := sourcePowerLawConfigWeight_nonneg _ _ ha config
    by_cases hd : (∑ x : Molecule n, truncatedBandValue (sourceShrinkingLower n) (sourceShrinkingUpper n) (config x)) <
        (49/50 : ℝ)*(sourceMoleculeCount n : ℝ)*sourceHighBandMean n
    · rw [if_pos hd]
      split_ifs <;> linarith only [hw]
    · have hi := mul_le_mul_of_nonneg_left (le_of_not_gt hd)
        (by positivity : 0 ≤ (19/20 : ℝ)/(sourceReactionCount n : ℝ))
      have hi' : sourceHighBandMeanIntensity n ≤ (19/20 : ℝ)/(sourceReactionCount n : ℝ)*
          ∑ x : Molecule n, truncatedBandValue (sourceShrinkingLower n) (sourceShrinkingUpper n) (config x) := by
        dsimp [sourceHighBandMeanIntensity]
        convert hi using 1
        ring
      have hx := Real.exp_le_exp.mpr (neg_le_neg hi')
      have hnot : ¬ 1-Real.exp (-((19/20 : ℝ)/(sourceReactionCount n : ℝ)*
          ∑ x : Molecule n, truncatedBandValue (sourceShrinkingLower n) (sourceShrinkingUpper n) (config x))) <
          (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) := by linarith only [hb, hx]
      simp only [if_neg hd, if_neg hnot, le_refl]

end
end PowerLawSmallRAF
