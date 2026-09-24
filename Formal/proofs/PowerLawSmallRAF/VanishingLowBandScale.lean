import proofs.PowerLawSmallRAF.SourceLowBandScale

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def vanishingLowBandWidth (n : Nat) : Nat := ⌊(n : ℝ)^(7/8 : ℝ)⌋₊
def sourceVanishingLowLower (n : Nat) : Nat := 2^vanishingLowBandWidth n

theorem vanishingLowBandWidth_tendsto : Tendsto vanishingLowBandWidth atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem vanishingLowBandWidth_relative_tendsto :
    Tendsto (fun n => (vanishingLowBandWidth n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hpow
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hfloor.mul hsmall
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heq : (n : ℝ)^(-(1/8 : ℝ)) = (n : ℝ)^(7/8 : ℝ)/(n : ℝ) := by
    rw [show -(1/8 : ℝ) = (7/8 : ℝ)-1 by ring, Real.rpow_sub hnpos, Real.rpow_one]
  dsimp only [Function.comp_apply]
  rw [heq]
  dsimp [vanishingLowBandWidth]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hnpos (7/8 : ℝ))]

theorem sourceVanishingLow_eventual_bounds :
    ∀ᶠ n : Nat in atTop, 4 ≤ n ∧ 2 ≤ sourceVanishingLowLower n ∧
      sourceVanishingLowLower n ≤ sourceShrinkingLower n ∧
      sourceShrinkingLower n < sourceReactionCount n := by
  have hl := vanishingLowBandWidth_relative_tendsto
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hh := shrinkingBandWidth_relative_tendsto
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  filter_upwards [eventually_ge_atTop 4,sourceShrinkingBand_eventual_bounds,
    vanishingLowBandWidth_tendsto.eventually (eventually_ge_atTop 1),hl,hh] with n hn hb hw hl hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsum : vanishingLowBandWidth n + shrinkingBandWidth n ≤ n := by
    have h1 := (div_lt_iff₀ hnpos).mp hl
    have h2 := (div_lt_iff₀ hnpos).mp hh
    have hs : (vanishingLowBandWidth n : ℝ)+(shrinkingBandWidth n : ℝ) ≤ n := by linarith
    exact_mod_cast hs
  refine ⟨hn,?_,?_,hb.2.2.2.2.1.trans_lt hb.2.2.2.2.2⟩
  · exact (show 2^1 ≤ 2^vanishingLowBandWidth n from Nat.pow_le_pow_right (by omega) hw)
  · exact Nat.pow_le_pow_right (by omega) (by omega : vanishingLowBandWidth n ≤ n-shrinkingBandWidth n)

theorem sourceVanishingLowLower_log_tendsto :
    Tendsto (fun n => Real.log (sourceVanishingLowLower n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have h := vanishingLowBandWidth_relative_tendsto.mul
    (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))
  simp only [zero_mul] at h
  convert h using 1
  funext n
  simp only [sourceVanishingLowLower,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  ring

def sourceVanishingLowIntegralProfile (n : Nat) : ℝ :=
  criticalPartialMass (-2) (Real.log (sourceShrinkingLower n : ℝ)/(n : ℝ)) -
    criticalPartialMass (-2) (Real.log (sourceVanishingLowLower n : ℝ)/(n : ℝ))

def sourceFullIntensity : ℝ := criticalPartialMass (-2) (Real.log 2)/(Real.pi^2/6)

theorem sourceVanishingLowIntegralProfile_tendsto :
    Tendsto sourceVanishingLowIntegralProfile atTop (𝓝 (criticalPartialMass (-2) (Real.log 2))) := by
  have hu := continuous_criticalPartialMass.continuousAt.tendsto.comp
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (-2 : ℝ)) atTop (𝓝 (-2))).prodMk_nhds
      sourceShrinkingLower_log_tendsto)
  have hl := continuous_criticalPartialMass.continuousAt.tendsto.comp
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (-2 : ℝ)) atTop (𝓝 (-2))).prodMk_nhds
      sourceVanishingLowLower_log_tendsto)
  have hzero : criticalPartialMass (-2) 0 = 0 := by simp [criticalPartialMass]
  have h := hu.sub hl
  rw [hzero,sub_zero] at h
  exact h

theorem sourceVanishingLow_integral_eq_profile (n : Nat) (hn : 0 < n) :
    ((∫ x in (1 : ℝ)..(sourceShrinkingLower n : ℝ), x^(-(1-2/(n : ℝ)))) -
      (∫ x in (1 : ℝ)..(sourceVanishingLowLower n : ℝ), x^(-(1-2/(n : ℝ))))) /
      (n : ℝ) = sourceVanishingLowIntegralProfile n := by
  have hU := movingWindowIntegral_eq_criticalPartialMass sourceShrinkingLower (-2) n hn
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hL := movingWindowIntegral_eq_criticalPartialMass sourceVanishingLowLower (-2) n hn
    (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hexp : -(1+(-2 : ℝ)/(n : ℝ)) = -(1-2/(n : ℝ)) := by ring
  simp only [hexp] at hU hL
  rw [sub_div,hU,hL]
  rfl

end
end PowerLawSmallRAF
