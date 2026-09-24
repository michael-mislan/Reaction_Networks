import proofs.PowerLawSmallRAF.ShrinkingBandScale
import proofs.PowerLawSmallRAF.SourceBandIntegralBound

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

def sourceShrinkingLower (n : Nat) : Nat := 2^(n-shrinkingBandWidth n)
def sourceShrinkingUpper (n : Nat) : Nat := 2^(n-shrinkingBandWidth n/20)

theorem sourceShrinkingBand_eventual_bounds :
    ∀ᶠ n : Nat in atTop, 4 ≤ n ∧ 0 < shrinkingBandWidth n ∧
      shrinkingBandWidth n < n ∧ 2 ≤ sourceShrinkingLower n ∧
      sourceShrinkingLower n ≤ sourceShrinkingUpper n ∧
      sourceShrinkingUpper n < sourceReactionCount n := by
  have hrel := shrinkingBandWidth_relative_tendsto (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [eventually_ge_atTop 4, hrel,
    shrinkingBandWidth_tendsto.eventually (eventually_ge_atTop 20)] with n hn hrel hh
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlt : shrinkingBandWidth n < n := by
    exact_mod_cast (div_lt_one hnpos).mp hrel
  have hj : 1 ≤ shrinkingBandWidth n / 20 := by omega
  have hjh : shrinkingBandWidth n / 20 ≤ shrinkingBandWidth n := Nat.div_le_self _ _
  refine ⟨hn, by omega, hlt, ?_, ?_, ?_⟩
  · exact (show 2^1 ≤ 2^(n-shrinkingBandWidth n) from
      Nat.pow_le_pow_right (by omega) (by omega))
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · apply lt_of_lt_of_le _ (sourceReactionCount_bounds hn).1
    exact Nat.pow_lt_pow_right (by omega) (by omega : n-shrinkingBandWidth n/20 < n)

private theorem dyadic_window_power (n k : Nat) (hn : 0 < n) (hk : k ≤ n) :
    (((2^(n-k) : Nat) : ℝ)^(2/(n : ℝ))) =
      4*Real.exp (-2*(k : ℝ)*Real.log 2/(n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  push_cast
  rw [Real.rpow_def_of_pos (by positivity), Real.log_pow, Nat.cast_sub hk]
  have he : ((n : ℝ)-(k : ℝ))*Real.log 2*(2/(n : ℝ)) =
      2*Real.log 2 + (-2*(k : ℝ)*Real.log 2/(n : ℝ)) := by
    field_simp
    ring
  rw [he, Real.exp_add]
  have hfour : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2 = Real.log 2+Real.log 2 by ring, Real.exp_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [hfour]

theorem sourceShrinkingBand_integral_eq_profile (n : Nat)
    (hn : 0 < n) (hh : 0 < shrinkingBandWidth n) (hhn : shrinkingBandWidth n ≤ n) :
    ((∫ x in (1 : ℝ)..(sourceShrinkingUpper n : ℝ), x ^ (-(1-2/(n : ℝ)))) -
      (∫ x in (1 : ℝ)..(sourceShrinkingLower n : ℝ), x ^ (-(1-2/(n : ℝ))))) /
      (shrinkingBandWidth n : ℝ) = shrinkingBandIntegralProfile n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hh0 : (shrinkingBandWidth n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hh)
  have hU := movingWindowIntegral_eq sourceShrinkingUpper (-2) (by norm_num) n
    (by omega) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hL := movingWindowIntegral_eq sourceShrinkingLower (-2) (by norm_num) n
    (by omega) (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  have hexp : -(1+(-2 : ℝ)/(n : ℝ)) = -(1-2/(n : ℝ)) := by ring
  simp only [hexp, neg_neg] at hU hL
  rw [sourceShrinkingUpper, dyadic_window_power n (shrinkingBandWidth n/20) hn
    ((Nat.div_le_self _ _).trans hhn)] at hU
  rw [sourceShrinkingLower, dyadic_window_power n (shrinkingBandWidth n) hn hhn] at hL
  rw [shrinkingBandIntegralProfile_eq_exp n hn hh]
  have hdiff := congrArg (fun x : ℝ => x * (n : ℝ)) (congrArg₂ (fun x y : ℝ => x-y) hU hL)
  dsimp only [sourceShrinkingUpper, sourceShrinkingLower]
  field_simp at hdiff ⊢
  nlinarith only [hdiff]

end
end PowerLawSmallRAF
