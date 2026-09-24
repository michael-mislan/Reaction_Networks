import proofs.PowerLawSmallRAF.SourceLowBandScale

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

def sourceLowBandMean (n : Nat) : ℝ :=
  sourceTruncatedBandMean (2-2/(n : ℝ)) n (sourceLowBandLower n) (sourceShrinkingLower n)

theorem sourceLowBandMean_tendsto :
    Tendsto (fun n : Nat => sourceLowBandMean n/(n : ℝ)) atTop
      (𝓝 (sourceLowBandIntegralLimit/(Real.pi^2/6))) := by
  let Z := fun n : Nat => zipfNormalizer (2-2/(n : ℝ))
  let I := fun n : Nat =>
    (∫ x in (1 : ℝ)..(sourceShrinkingLower n : ℝ), x^(-(1-2/(n : ℝ)))) -
      (∫ x in (1 : ℝ)..(sourceLowBandLower n : ℝ), x^(-(1-2/(n : ℝ))))
  have hz : Tendsto Z atTop (𝓝 (Real.pi^2/6)) := by
    simpa only [Z, sub_eq_add_neg, neg_div] using zipfNormalizer_source_window (-2)
  have he : Tendsto (fun n : Nat => (2+Z n)/(n : ℝ)) atTop (𝓝 0) :=
    (tendsto_const_nhds.add hz).div_atTop (tendsto_natCast_atTop_atTop (R := ℝ))
  have hevent : ∀ᶠ n : Nat in atTop,
      |sourceLowBandMean n*Z n/(n : ℝ)-sourceLowBandIntegralProfile n| ≤ (2+Z n)/(n : ℝ) := by
    filter_upwards [sourceLowBand_eventual_bounds] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ha : 1 < 2-2/(n : ℝ) := by
      have h : (2 : ℝ)/(n : ℝ) < 1 := (div_lt_one hnpos).mpr (by exact_mod_cast (show 2 < n by omega))
      linarith
    have hb := sourceTruncatedBandMean_unshifted_integral_error (2-2/(n : ℝ)) n
      (sourceLowBandLower n) (sourceShrinkingLower n) ha (by omega) hn.2.1 hn.2.2.1 hn.2.2.2
    have hexp : -((2-2/(n : ℝ))-1) = -(1-2/(n : ℝ)) := by ring
    have hb' : |sourceLowBandMean n*Z n-I n| ≤ 2+Z n := by
      simpa only [sourceLowBandMean,Z,I,hexp] using hb
    have hid : I n/(n : ℝ) = sourceLowBandIntegralProfile n :=
      sourceLowBand_integral_eq_profile n (by omega)
    rw [← hid, ← sub_div, abs_div, abs_of_pos hnpos]
    exact div_le_div_of_nonneg_right hb' hnpos.le
  have hw : Tendsto (fun n : Nat => sourceLowBandMean n*Z n/(n : ℝ)) atTop
      (𝓝 sourceLowBandIntegralLimit) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa only [sub_zero] using sourceLowBandIntegralProfile_tendsto.sub he)
      (by simpa only [add_zero] using sourceLowBandIntegralProfile_tendsto.add he)
    · filter_upwards [hevent] with n hn
      linarith only [(abs_le.mp hn).1]
    · filter_upwards [hevent] with n hn
      linarith only [(abs_le.mp hn).2]
  have hquot := hw.div hz (by positivity : Real.pi^2/6 ≠ 0)
  apply hquot.congr'
  filter_upwards [hz (Ioi_mem_nhds (by positivity : (0 : ℝ) < Real.pi^2/6))] with n hn
  change 0 < Z n at hn
  change (sourceLowBandMean n*Z n/(n : ℝ))/Z n = sourceLowBandMean n/(n : ℝ)
  field_simp [ne_of_gt hn]

theorem sourceLowBandDensity_tendsto :
    Tendsto (fun n : Nat => ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceLowBandMean n)
      atTop (𝓝 (sourceLowBandIntegralLimit/(Real.pi^2/6))) := by
  have hcat : Tendsto (fun n : Nat => (n : ℝ)*(sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))
      atTop (𝓝 1) := by
    simpa only [inv_div, inv_one] using sourceReactionCount_div_nat_molecule_tendsto_one.inv₀ one_ne_zero
  have h := hcat.mul sourceLowBandMean_tendsto
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

end
end PowerLawSmallRAF
