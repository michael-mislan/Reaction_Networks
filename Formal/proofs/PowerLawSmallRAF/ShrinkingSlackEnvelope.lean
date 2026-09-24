import proofs.PowerLawSmallRAF.ShrinkingSlackScale

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def sourceVanishingRowErrorEnvelope (n : Nat) : ℝ :=
  (sourceMoleculeCount n : ℝ)*Real.exp (-sourceVanishingRowSlack n^2*(sourceVanishingLowLower n : ℝ)/4)

theorem sourceVanishingRowErrorEnvelope_eventually_le :
    ∀ᶠ n : Nat in atTop, sourceVanishingRowErrorEnvelope n ≤ Real.exp (-(n : ℝ)) := by
  filter_upwards [sourceVanishingLowLower_eventually_quadratic] with n hb
  have hx : (0 : ℝ) < ((n+1 : Nat) : ℝ) := by positivity
  have hL : 8*((n+1 : Nat) : ℝ) ≤ (sourceVanishingLowLower n : ℝ)/((n+1 : Nat) : ℝ) := by
    apply (le_div_iff₀ hx).mpr
    nlinarith
  have heps := mul_le_mul_of_nonneg_right (sourceVanishingRowSlack_sq_lower n)
    (Nat.cast_nonneg (sourceVanishingLowLower n) : (0 : ℝ) ≤ sourceVanishingLowLower n)
  have hprod : 8*((n+1 : Nat) : ℝ) ≤ sourceVanishingRowSlack n^2*(sourceVanishingLowLower n : ℝ) := by
    rw [one_div,mul_comm (_⁻¹),← div_eq_mul_inv] at heps
    exact hL.trans heps
  have hN : (sourceMoleculeCount n : ℝ) ≤ (2 : ℝ)^(n+1) := by
    exact_mod_cast (show sourceMoleculeCount n ≤ 2^(n+1) from Nat.sub_le _ _)
  have hpow : (2 : ℝ)^(n+1) = Real.exp (((n+1 : Nat) : ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hlog := mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) hx.le
  calc
    _ ≤ (2 : ℝ)^(n+1)*Real.exp (-sourceVanishingRowSlack n^2*(sourceVanishingLowLower n : ℝ)/4) :=
      mul_le_mul_of_nonneg_right hN (Real.exp_pos _).le
    _ ≤ _ := by
      rw [hpow,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      push_cast at hprod hlog ⊢
      nlinarith

theorem sourceVanishingRowErrorEnvelope_tendsto_zero :
    Tendsto sourceVanishingRowErrorEnvelope atTop (𝓝 0) := by
  have hneg : Tendsto (fun n : Nat => -(n : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (Real.tendsto_exp_atBot.comp hneg) _ sourceVanishingRowErrorEnvelope_eventually_le
  filter_upwards with n
  exact mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le

end
end PowerLawSmallRAF
