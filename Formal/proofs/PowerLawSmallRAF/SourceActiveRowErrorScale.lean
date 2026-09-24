import proofs.PowerLawSmallRAF.SourceOwnerLengthScales

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

theorem sourceLowBandLower_tendsto_atTop : Tendsto sourceLowBandLower atTop atTop := by
  have hd : Tendsto (fun n : Nat => n/100) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (100*b)] with n hn
    omega
  exact (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2 : Nat))).comp hd

theorem nat_div_sourceLowBandLower_tendsto_zero :
    Tendsto (fun n : Nat => (n : ℝ)/(sourceLowBandLower n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds nat_div_two_pow_twohundredth_tendsto_zero
  · filter_upwards with n
    positivity
  · filter_upwards with n
    simp only [sourceLowBandLower, Nat.cast_pow, Nat.cast_ofNat]
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg n) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (by omega))

def sourceActiveRowErrorEnvelope (n : Nat) : ℝ :=
  (sourceMoleculeCount n : ℝ)*Real.exp (-(sourceLowBandLower n : ℝ)/1600)

theorem sourceActiveRowErrorEnvelope_tendsto_zero :
    Tendsto sourceActiveRowErrorEnvelope atTop (𝓝 0) := by
  have hA := (tendsto_natCast_atTop_atTop (R := ℝ)).comp sourceLowBandLower_tendsto_atTop
  have hi : Tendsto (fun n : Nat => (1 : ℝ)/(sourceLowBandLower n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hA
  have hr : Tendsto (fun n : Nat => ((n+1 : Nat) : ℝ)/(sourceLowBandLower n : ℝ)) atTop (𝓝 0) := by
    have h := nat_div_sourceLowBandLower_tendsto_zero.add hi
    simp only [add_zero] at h
    convert h using 1
    funext n
    push_cast
    ring
  have hc : Tendsto (fun n : Nat => (1/1600 : ℝ)-
      ((n+1 : Nat) : ℝ)/(sourceLowBandLower n : ℝ)*Real.log 2) atTop (𝓝 (1/1600 : ℝ)) := by
    simpa only [zero_mul, sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : Nat => (1/1600 : ℝ)) atTop (𝓝 (1/1600 : ℝ))).sub
        (hr.mul (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2))))
  have ht := hA.atTop_mul_pos (by norm_num : (0 : ℝ) < 1/1600) hc
  have hn : Tendsto (fun n : Nat => -((sourceLowBandLower n : ℝ)*((1/1600 : ℝ)-
      ((n+1 : Nat) : ℝ)/(sourceLowBandLower n : ℝ)*Real.log 2))) atTop atBot := by
    rw [tendsto_atBot]
    intro B
    filter_upwards [ht.eventually_ge_atTop (-B)] with n hn
    dsimp only [Function.comp_apply] at hn
    linarith
  have he : Tendsto (fun n : Nat => Real.exp (((n+1 : Nat) : ℝ)*Real.log 2-
      (sourceLowBandLower n : ℝ)/1600)) atTop (𝓝 0) := by
    apply (Real.tendsto_exp_atBot.comp hn).congr'
    filter_upwards with n
    have hA0 : (sourceLowBandLower n : ℝ) ≠ 0 := by
      exact_mod_cast (pow_ne_zero _ (by decide : (2 : Nat) ≠ 0))
    simp only [Function.comp_apply]
    congr 1
    field_simp
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds he
  · filter_upwards with n
    exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le
  · filter_upwards with n
    have hN : (sourceMoleculeCount n : ℝ) ≤ (2 : ℝ)^(n+1) := by
      exact_mod_cast (show sourceMoleculeCount n ≤ 2^(n+1) from Nat.sub_le _ _)
    calc
      _ ≤ (2 : ℝ)^(n+1)*Real.exp (-(sourceLowBandLower n : ℝ)/1600) :=
        mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
      _ = _ := by
        rw [Real.exp_sub, ← Real.log_pow, Real.exp_log (by positivity : (0 : ℝ) < (2 : ℝ)^(n+1))]
        rw [show -(sourceLowBandLower n : ℝ)/1600 = -((sourceLowBandLower n : ℝ)/1600) by ring,
          Real.exp_neg]
        rfl

end
end PowerLawSmallRAF
