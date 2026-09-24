import proofs.PowerLawSmallRAF.SourceShrinkingBandMean

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

def sourceLowBandLower (n : Nat) : Nat := 2^(n/100)

theorem sourceLowBand_eventual_bounds :
    ∀ᶠ n : Nat in atTop, 4 ≤ n ∧ 2 ≤ sourceLowBandLower n ∧
      sourceLowBandLower n ≤ sourceShrinkingLower n ∧
      sourceShrinkingLower n < sourceReactionCount n := by
  have hr := shrinkingBandWidth_relative_tendsto
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_ge_atTop 200, sourceShrinkingBand_eventual_bounds, hr] with n hn hb hr
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh : 2*shrinkingBandWidth n < n := by
    have h := (div_lt_iff₀ hnpos).mp hr
    have h' : (2 : ℝ)*(shrinkingBandWidth n : ℝ) < n := by linarith
    exact_mod_cast h'
  refine ⟨by omega, ?_, ?_, hb.2.2.2.2.1.trans_lt hb.2.2.2.2.2⟩
  · exact (show 2^1 ≤ 2^(n/100) from Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.pow_le_pow_right (by omega) (by omega : n/100 ≤ n-shrinkingBandWidth n)

theorem sourceLowBandLower_log_tendsto :
    Tendsto (fun n : Nat => Real.log (sourceLowBandLower n : ℝ)/(n : ℝ)) atTop
      (𝓝 (Real.log 2/100)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 1/100)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h' : Tendsto (fun n : Nat => ((n/100 : Nat) : ℝ)/(n : ℝ)) atTop (𝓝 (1/100 : ℝ)) := by
    simpa only [Function.comp_def, one_div, inv_mul_eq_div, Nat.floor_div_ofNat,
      Nat.floor_natCast] using h
  have hm := h'.mul (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))
  convert hm using 1
  · funext n
    simp only [sourceLowBandLower, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    ring
  · congr 1
    ring

theorem sourceShrinkingLower_log_tendsto :
    Tendsto (fun n : Nat => Real.log (sourceShrinkingLower n : ℝ)/(n : ℝ)) atTop
      (𝓝 (Real.log 2)) := by
  have h := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
    shrinkingBandWidth_relative_tendsto).mul
    (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))
  have h' : Tendsto (fun n : Nat => (1-(shrinkingBandWidth n : ℝ)/(n : ℝ))*Real.log 2)
      atTop (𝓝 (Real.log 2)) := by simpa using h
  apply h'.congr'
  filter_upwards [sourceShrinkingBand_eventual_bounds] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simp only [sourceShrinkingLower, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow,
    Nat.cast_sub hn.2.2.1.le]
  field_simp

def sourceLowBandIntegralProfile (n : Nat) : ℝ :=
  criticalPartialMass (-2) (Real.log (sourceShrinkingLower n : ℝ)/(n : ℝ)) -
    criticalPartialMass (-2) (Real.log (sourceLowBandLower n : ℝ)/(n : ℝ))

def sourceLowBandIntegralLimit : ℝ :=
  criticalPartialMass (-2) (Real.log 2) - criticalPartialMass (-2) (Real.log 2/100)

theorem sourceLowBandIntegralProfile_tendsto :
    Tendsto sourceLowBandIntegralProfile atTop (𝓝 sourceLowBandIntegralLimit) := by
  have hu := continuous_criticalPartialMass.continuousAt.tendsto.comp
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (-2 : ℝ)) atTop (𝓝 (-2))).prodMk_nhds
      sourceShrinkingLower_log_tendsto)
  have hl := continuous_criticalPartialMass.continuousAt.tendsto.comp
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (-2 : ℝ)) atTop (𝓝 (-2))).prodMk_nhds
      sourceLowBandLower_log_tendsto)
  exact hu.sub hl

theorem sourceLowBand_integral_eq_profile (n : Nat) (hn : 0 < n) :
    ((∫ x in (1 : ℝ)..(sourceShrinkingLower n : ℝ), x^(-(1-2/(n : ℝ)))) -
      (∫ x in (1 : ℝ)..(sourceLowBandLower n : ℝ), x^(-(1-2/(n : ℝ))))) /
      (n : ℝ) = sourceLowBandIntegralProfile n := by
  have hU := movingWindowIntegral_eq_criticalPartialMass sourceShrinkingLower (-2) n hn
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hL := movingWindowIntegral_eq_criticalPartialMass sourceLowBandLower (-2) n hn
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hexp : -(1+(-2 : ℝ)/(n : ℝ)) = -(1-2/(n : ℝ)) := by ring
  simp only [hexp] at hU hL
  rw [sub_div, hU, hL]
  rfl

end
end PowerLawSmallRAF
