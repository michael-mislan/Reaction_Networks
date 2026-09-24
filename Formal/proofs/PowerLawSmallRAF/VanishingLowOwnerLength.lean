import proofs.PowerLawSmallRAF.VanishingLowBandScale
import proofs.PowerLawSmallRAF.SourceShortOwnerExclusions

namespace PowerLawSmallRAF
open RAF.Polymer RAF.Concrete Filter Topology
noncomputable section

/-- Subtract the existing high-band width so the short-owner error reduces
exactly to an already verified exponential ratio. -/
def sourceVanishingLowOwnerLength (n : Nat) : Nat := vanishingLowBandWidth n-shrinkingBandWidth n

theorem vanishingLowBandWidth_ge_shrinking (n : Nat) (hn : 1 ≤ n) :
    shrinkingBandWidth n ≤ vanishingLowBandWidth n := by
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by norm_num : (3/4 : ℝ) ≤ 7/8)

theorem vanishingLowBandWidth_le_nat (n : Nat) (hn : 1 ≤ n) : vanishingLowBandWidth n ≤ n := by
  apply Nat.floor_le_of_le
  have h := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    (by norm_num : (7/8 : ℝ) ≤ 1)
  simpa only [Real.rpow_one] using h

theorem sourceVanishingLowShortOwnerFailureMass_tendsto_zero :
    Tendsto (fun n : Nat => sourceShortOwnerFailureMass (2-2/(n : ℝ)) n
      (sourceVanishingLowOwnerLength n) (sourceVanishingLowLower n)) atTop (𝓝 0) := by
  apply source_short_owner_failure_tendsto_of_ratio
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact ⟨(Nat.sub_le _ _).trans (vanishingLowBandWidth_le_nat n hn),pow_pos (by decide) _⟩
  · apply nat_div_two_pow_shrinking_tendsto_zero.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hp : (2 : ℝ)^(sourceVanishingLowOwnerLength n)*(2 : ℝ)^shrinkingBandWidth n =
        (sourceVanishingLowLower n : ℝ) := by
      rw [← pow_add]
      simp only [sourceVanishingLowOwnerLength,sourceVanishingLowLower,Nat.cast_pow,Nat.cast_ofNat,
        Nat.sub_add_cancel (vanishingLowBandWidth_ge_shrinking n hn)]
    rw [← hp]
    field_simp

end
end PowerLawSmallRAF
