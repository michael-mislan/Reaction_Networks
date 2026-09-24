import proofs.PowerLawSmallRAF.SourceShrinkingBandMean
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

/-- The actual capped-Zipf degree mean in the explicit rounded high band,
normalized by its diverging logarithmic width. -/
theorem sourceShrinkingBandMean_tendsto :
    Tendsto (fun n : Nat =>
      sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceShrinkingLower n)
        (sourceShrinkingUpper n) / (shrinkingBandWidth n : ℝ)) atTop
      (𝓝 (((19/5 : ℝ)*Real.log 2)/(Real.pi^2/6))) := by
  let M := fun n : Nat => sourceTruncatedBandMean (2-2/(n : ℝ)) n
    (sourceShrinkingLower n) (sourceShrinkingUpper n)
  let Z := fun n : Nat => zipfNormalizer (2-2/(n : ℝ))
  let I := fun n : Nat =>
    (∫ x in (1 : ℝ)..(sourceShrinkingUpper n : ℝ), x^(-(1-2/(n : ℝ)))) -
      (∫ x in (1 : ℝ)..(sourceShrinkingLower n : ℝ), x^(-(1-2/(n : ℝ))))
  have hz : Tendsto Z atTop (𝓝 (Real.pi^2/6)) := by
    simpa only [Z, sub_eq_add_neg, neg_div] using zipfNormalizer_source_window (-2)
  have hh := (tendsto_natCast_atTop_atTop (R := ℝ)).comp shrinkingBandWidth_tendsto
  have he : Tendsto (fun n => (2+Z n)/(shrinkingBandWidth n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds.add hz).div_atTop hh
  have hw : Tendsto (fun n => M n*Z n/(shrinkingBandWidth n : ℝ)) atTop
      (𝓝 ((19/5 : ℝ)*Real.log 2)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using shrinkingBandIntegralProfile_tendsto.sub he)
      (by simpa only [add_zero] using shrinkingBandIntegralProfile_tendsto.add he)
    · filter_upwards [sourceShrinkingBand_eventual_bounds] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hhpos : (0 : ℝ) < shrinkingBandWidth n := by exact_mod_cast hn.2.1
      have ha : 1 < 2-2/(n : ℝ) := by
        have hd : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
        linarith
      have hb := sourceTruncatedBandMean_unshifted_integral_error (2-2/(n : ℝ)) n
        (sourceShrinkingLower n) (sourceShrinkingUpper n) ha (by omega) hn.2.2.2.1
        hn.2.2.2.2.1 hn.2.2.2.2.2
      have hexp : -((2-2/(n : ℝ))-1) = -(1-2/(n : ℝ)) := by ring
      have hb' : |M n*Z n-I n| ≤ 2+Z n := by simpa only [M,Z,I,hexp] using hb
      have hid : I n/(shrinkingBandWidth n : ℝ) = shrinkingBandIntegralProfile n :=
        sourceShrinkingBand_integral_eq_profile n (by omega) hn.2.1 hn.2.2.1.le
      rw [← hid, ← sub_div]
      exact div_le_div_of_nonneg_right (by linarith only [(abs_le.mp hb').1]) hhpos.le
    · filter_upwards [sourceShrinkingBand_eventual_bounds] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hhpos : (0 : ℝ) < shrinkingBandWidth n := by exact_mod_cast hn.2.1
      have ha : 1 < 2-2/(n : ℝ) := by
        have hd : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
        linarith
      have hb := sourceTruncatedBandMean_unshifted_integral_error (2-2/(n : ℝ)) n
        (sourceShrinkingLower n) (sourceShrinkingUpper n) ha (by omega) hn.2.2.2.1
        hn.2.2.2.2.1 hn.2.2.2.2.2
      have hexp : -((2-2/(n : ℝ))-1) = -(1-2/(n : ℝ)) := by ring
      have hb' : |M n*Z n-I n| ≤ 2+Z n := by simpa only [M,Z,I,hexp] using hb
      have hid : I n/(shrinkingBandWidth n : ℝ) = shrinkingBandIntegralProfile n :=
        sourceShrinkingBand_integral_eq_profile n (by omega) hn.2.1 hn.2.2.1.le
      rw [← hid, ← add_div]
      exact div_le_div_of_nonneg_right (by linarith only [(abs_le.mp hb').2]) hhpos.le
  have hquot := hw.div hz (by positivity : Real.pi^2/6 ≠ 0)
  apply hquot.congr'
  filter_upwards [hz (Ioi_mem_nhds (by positivity : (0 : ℝ) < Real.pi^2/6))] with n hn
  change 0 < Z n at hn
  change (M n*Z n/(shrinkingBandWidth n : ℝ))/Z n = M n/(shrinkingBandWidth n : ℝ)
  field_simp [ne_of_gt hn]

/-- The actual high-band expected channel density has order n^(-1/4),
with the coefficient required by the proposed source construction. -/
theorem sourceShrinkingBandDensity_tendsto :
    Tendsto (fun n : Nat => (n : ℝ)^(1/4 : ℝ) *
      ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ)) *
      sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceShrinkingLower n)
        (sourceShrinkingUpper n)) atTop
      (𝓝 (((19/5 : ℝ)*Real.log 2)/(Real.pi^2/6))) := by
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hcatalog : Tendsto (fun n : Nat =>
      (n : ℝ)*(sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ)) atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using
      sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have h := (hfloor.mul hcatalog).mul sourceShrinkingBandMean_tendsto
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [sourceShrinkingBand_eventual_bounds] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh0 : (shrinkingBandWidth n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn.2.1)
  have hp0 : (n : ℝ)^(3/4 : ℝ) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hnpos _)
  have hp : (n : ℝ)^(1/4 : ℝ) = (n : ℝ)/(n : ℝ)^(3/4 : ℝ) := by
    rw [show (1/4 : ℝ) = 1-(3/4 : ℝ) by ring, Real.rpow_sub hnpos, Real.rpow_one]
  dsimp only [Function.comp_apply]
  change ((shrinkingBandWidth n : ℝ)/(n : ℝ)^(3/4 : ℝ)) *
    ((n : ℝ)*(sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ)) *
    (sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceShrinkingLower n)
      (sourceShrinkingUpper n)/(shrinkingBandWidth n : ℝ)) = _
  rw [hp]
  field_simp

/-- The high-band mean pays both the two-percent concentration reserve and
the five-percent fixed-degree coupling slack, with room for p=1.45 n^(-1/4). -/
theorem sourceShrinkingBand_retained_budget :
    ∀ᶠ n : Nat in atTop,
      (29/20 : ℝ)*(n : ℝ)^(-(1/4 : ℝ)) ≤
      (49/50 : ℝ)*(19/20 : ℝ)*
        ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*
        sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceShrinkingLower n)
          (sourceShrinkingUpper n) := by
  have hmargin : (29/20 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
      (((19/5 : ℝ)*Real.log 2)/(Real.pi^2/6)) := by
    have hp : Real.pi^2 < (3.15 : ℝ)^2 := by
      nlinarith [Real.pi_pos, Real.pi_lt_d2]
    rw [← mul_div_assoc, lt_div_iff₀ (by positivity)]
    nlinarith [Real.log_two_gt_d9]
  have h := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (49/50 : ℝ)*(19/20 : ℝ))
    atTop (𝓝 ((49/50 : ℝ)*(19/20 : ℝ)))).mul sourceShrinkingBandDensity_tendsto)
      (Ioi_mem_nhds hmargin)
  filter_upwards [h, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp : 0 < (n : ℝ)^(1/4 : ℝ) := Real.rpow_pos_of_pos hnpos _
  change (29/20 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
    ((n : ℝ)^(1/4 : ℝ)*((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*
      sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceShrinkingLower n)
        (sourceShrinkingUpper n)) at hn
  rw [Real.rpow_neg (le_of_lt hnpos), ← div_eq_mul_inv]
  apply (div_le_iff₀ hp).mpr
  nlinarith only [hn.le]

end
end PowerLawSmallRAF
