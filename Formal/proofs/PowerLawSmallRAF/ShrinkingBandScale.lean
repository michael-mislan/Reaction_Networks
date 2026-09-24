import proofs.PowerLawSmallRAF.MovingBandMass
import Mathlib.Algebra.Order.Floor.Semifield

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def shrinkingBandWidth (n : Nat) : Nat := ⌊(n : ℝ) ^ (3/4 : ℝ)⌋₊

theorem shrinkingBandWidth_tendsto : Tendsto shrinkingBandWidth atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem shrinkingBandWidth_relative_tendsto :
    Tendsto (fun n => (shrinkingBandWidth n : ℝ) / (n : ℝ)) atTop (𝓝 0) := by
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hfloor := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hpow
  have hsmall := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := hfloor.mul hsmall
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have heq : (n : ℝ)^(-(1/4 : ℝ)) = (n : ℝ)^(3/4 : ℝ)/(n : ℝ) := by
    rw [show -(1/4 : ℝ) = (3/4 : ℝ)-1 by ring, Real.rpow_sub hnpos, Real.rpow_one]
  dsimp only [Function.comp_apply]
  rw [heq]
  dsimp [shrinkingBandWidth]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hnpos (3/4 : ℝ))]

theorem shrinkingBandWidth_twentieth_tendsto :
    Tendsto (fun n => ((shrinkingBandWidth n / 20 : Nat) : ℝ) /
      (shrinkingBandWidth n : ℝ)) atTop (𝓝 (1/20 : ℝ)) := by
  have h := (tendsto_nat_floor_mul_div_atTop (by norm_num : (0 : ℝ) ≤ 1/20)).comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp shrinkingBandWidth_tendsto)
  simpa only [Function.comp_def, one_div, inv_mul_eq_div, Nat.floor_div_ofNat,
    Nat.floor_natCast] using h

def shrinkingBandIntegralProfile (n : Nat) : ℝ :=
  4 * (criticalPartialMass (2*(shrinkingBandWidth n : ℝ)/(n : ℝ)) (Real.log 2) -
    criticalPartialMass (2*(shrinkingBandWidth n : ℝ)/(n : ℝ))
      (((shrinkingBandWidth n / 20 : Nat) : ℝ)/(shrinkingBandWidth n : ℝ)*Real.log 2))

/-- The explicit rounded logarithmic-window profile. The source endpoint
`+1` corrections and normalizer are separate obligations. -/
theorem shrinkingBandIntegralProfile_tendsto :
    Tendsto shrinkingBandIntegralProfile atTop (𝓝 ((19/5 : ℝ)*Real.log 2)) := by
  have ht : Tendsto (fun n => 2*(shrinkingBandWidth n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_div_assoc] using
      (tendsto_const_nhds.mul shrinkingBandWidth_relative_tendsto :
        Tendsto (fun n => 2*((shrinkingBandWidth n : ℝ)/(n : ℝ))) atTop (𝓝 (2*0)))
  have hc := shrinkingBandWidth_twentieth_tendsto.mul
    (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))
  have hu := continuous_criticalPartialMass.continuousAt.tendsto.comp
    (ht.prodMk_nhds (tendsto_const_nhds :
      Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2))))
  have hl := continuous_criticalPartialMass.continuousAt.tendsto.comp (ht.prodMk_nhds hc)
  have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (4 : ℝ)) atTop (𝓝 4)).mul (hu.sub hl)
  convert h using 1
  congr 1
  simp [criticalPartialMass]
  ring

theorem shrinkingBandIntegralProfile_eq_exp (n : Nat)
    (hn : 0 < n) (hh : 0 < shrinkingBandWidth n) :
    shrinkingBandIntegralProfile n =
      2 * (Real.exp (-2*((shrinkingBandWidth n / 20 : Nat) : ℝ)*Real.log 2/(n : ℝ)) -
        Real.exp (-2*(shrinkingBandWidth n : ℝ)*Real.log 2/(n : ℝ))) /
        ((shrinkingBandWidth n : ℝ)/(n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hh0 : (shrinkingBandWidth n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  have ht : 2*(shrinkingBandWidth n : ℝ)/(n : ℝ) ≠ 0 := by positivity
  unfold shrinkingBandIntegralProfile criticalPartialMass
  rw [integral_exp_neg_mul _ ht, integral_exp_neg_mul _ ht]
  have harg : -(2*(shrinkingBandWidth n : ℝ)/(n : ℝ)) *
      (((shrinkingBandWidth n / 20 : Nat) : ℝ)/(shrinkingBandWidth n : ℝ)*Real.log 2) =
      -2*((shrinkingBandWidth n / 20 : Nat) : ℝ)*Real.log 2/(n : ℝ) := by
    field_simp
  rw [harg]
  have harg2 : -(2*(shrinkingBandWidth n : ℝ)/(n : ℝ))*Real.log 2 =
      -2*(shrinkingBandWidth n : ℝ)*Real.log 2/(n : ℝ) := by ring
  rw [harg2]
  field_simp
  ring

theorem shrinkingBand_exp_window_tendsto :
    Tendsto (fun n : Nat =>
      2 * (Real.exp (-2*((shrinkingBandWidth n / 20 : Nat) : ℝ)*Real.log 2/(n : ℝ)) -
        Real.exp (-2*(shrinkingBandWidth n : ℝ)*Real.log 2/(n : ℝ))) /
        ((shrinkingBandWidth n : ℝ)/(n : ℝ))) atTop (𝓝 ((19/5 : ℝ)*Real.log 2)) := by
  apply shrinkingBandIntegralProfile_tendsto.congr'
  filter_upwards [eventually_ge_atTop 1,
    shrinkingBandWidth_tendsto.eventually (eventually_ge_atTop 1)] with n hn hh
  exact shrinkingBandIntegralProfile_eq_exp n (by omega) (by omega)

end
end PowerLawSmallRAF
