import proofs.PowerLawSmallRAF.VanishingTargetScale
import proofs.PowerLawSmallRAF.BoundedTargetSourceDock

namespace PowerLawSmallRAF
open RAF.Polymer Filter Topology
noncomputable section

def vanishingLowTargetError (C n : Nat) : ℝ :=
  ((C : ℝ)+(2 : ℝ)^(targetNucleusLength n+1))*
    (Real.exp (-targetIntensity n*(sourceVanishingLowOwnerLength n : ℝ)/2)+
      2*(n : ℝ)^2*Real.exp (-targetIntensity n*(targetNucleusLength n : ℝ)^2/32))

theorem vanishingLowTargetError_zero_tendsto :
    Tendsto (vanishingLowTargetError 0) atTop (𝓝 0) := by
  have hd := target_exp_of_negative_ratio _ (by norm_num : (0 : ℝ)-29/10 < 0)
    (targetDensityLog_ratio _ lowTargetLogCount_ratio)
  have hs := vanishingTargetDirectExp_tendsto_zero.add hd
  simp only [add_zero] at hs
  apply hs.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← targetUnionEnvelope_eq_logs _ _ n (by omega)]
  have h2 := Real.exp_log (pow_pos (by norm_num : (0 : ℝ)<2) (targetNucleusLength n+1))
  rw [Real.log_pow] at h2
  unfold targetUnionEnvelope lowTargetLogCount vanishingLowTargetError
  rw [show ((targetNucleusLength n : ℝ)+1)*Real.log 2 =
    ((targetNucleusLength n+1 : Nat) : ℝ)*Real.log 2 by push_cast; rfl,h2]
  simp only [Nat.cast_zero,zero_add]

theorem vanishingLowTargetError_le (C n : Nat) :
    vanishingLowTargetError C n ≤ ((C : ℝ)+1)*vanishingLowTargetError 0 n := by
  have hpow : (1 : ℝ) ≤ (2 : ℝ)^(targetNucleusLength n+1) := one_le_pow₀ (by norm_num)
  have hcount : (C : ℝ)+(2 : ℝ)^(targetNucleusLength n+1) ≤
      ((C : ℝ)+1)*(2 : ℝ)^(targetNucleusLength n+1) := by
    nlinarith [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
  unfold vanishingLowTargetError
  simp only [Nat.cast_zero,zero_add,← mul_assoc]
  exact mul_le_mul_of_nonneg_right hcount (by positivity)

/-- Any fixed finite seed catalogue adds only a constant multiplicative
factor to the already vanishing target envelope. -/
theorem vanishingLowTargetError_tendsto_zero (C : Nat) :
    Tendsto (vanishingLowTargetError C) atTop (𝓝 0) := by
  have hu := vanishingLowTargetError_zero_tendsto.const_mul ((C : ℝ)+1)
  simp only [mul_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with n
    unfold vanishingLowTargetError
    positivity
  · filter_upwards with n
    exact vanishingLowTargetError_le C n

/-- Uniform bounded-witness target estimate with the revised actual-owner
length scale and an arbitrary fixed seed-base budget. -/
theorem source_bounded_vanishing_low_uniform_bound :
    ∀ᶠ n : Nat in atTop, ∀ C : Nat, ∀ q : ℝ, targetIntensity n ≤ q → q ≤ 1 →
      ∀ W : Finset LigationWord,
      (W.card : ℝ) ≤ (C : ℝ)+(2 : ℝ)^(targetNucleusLength n+1) →
      (∀ w ∈ W, sourceVanishingLowOwnerLength n ≤ w.length ∧ w.length ≤ n) →
      ∀ T : Finset (Reaction n) → Finset (Reaction n),
      sourceBoundedTargetsFailureMass q n (targetNucleusLength n) W T ≤ vanishingLowTargetError C n := by
  filter_upwards [targetUnion_eventual_conditions,sourceVanishingLowOwnerLength_eventually_nucleus] with n hn hLm
  intro C q hpq hq W hK hW T
  exact source_bounded_union_bound_with_intensity_floor hn.1 hpq hq n (targetNucleusLength n)
    (sourceVanishingLowOwnerLength n) W hK hW T hn.2.2.1 hLm hn.2.2.2.2.2

end
end PowerLawSmallRAF
