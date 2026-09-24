import proofs.PowerLawSmallRAF.VanishingLowIntensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section

def sourceVanishingRowSlack (n : Nat) : ℝ := ((n+1 : Nat) : ℝ)^(-(1/8 : ℝ))

theorem sourceVanishingRowSlack_pos (n : Nat) : 0 < sourceVanishingRowSlack n := by
  exact Real.rpow_pos_of_pos (by positivity) _

theorem sourceVanishingRowSlack_tendsto : Tendsto sourceVanishingRowSlack atTop (𝓝 0) := by
  have h := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : ℝ)) atTop (𝓝 1)).sub
    sourceVanishingLowRetention_tendsto
  have he : (fun n => 1-sourceVanishingLowRetention n) = sourceVanishingRowSlack := by
    funext n
    simp [sourceVanishingLowRetention,sourceVanishingRowSlack]
  rw [he,sub_self] at h
  exact h

theorem sourceVanishingRowSlack_sq_lower (n : Nat) :
    1/((n+1 : Nat) : ℝ) ≤ sourceVanishingRowSlack n^2 := by
  have hx : (1 : ℝ) ≤ ((n+1 : Nat) : ℝ) := by exact_mod_cast (show 1 ≤ n+1 by omega)
  have h := Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (-1 : ℝ) ≤ -(1/4 : ℝ))
  rw [Real.rpow_neg_one] at h
  have he : sourceVanishingRowSlack n^2 = ((n+1 : Nat) : ℝ)^(-(1/4 : ℝ)) := by
    unfold sourceVanishingRowSlack
    rw [← Real.rpow_mul_natCast (by positivity)]
    norm_num
  simpa only [he,one_div] using h

theorem sourceVanishingLowLower_div_sq_tendsto_atTop :
    Tendsto (fun n : Nat => (sourceVanishingLowLower n : ℝ)/(n : ℝ)^2) atTop atTop := by
  have hp := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hf := (tendsto_nat_floor_div_atTop (R := ℝ)).comp hp
  have hl := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 7/8)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := (hf.mul (tendsto_const_nhds : Tendsto (fun _ : Nat => Real.log 2) atTop (𝓝 (Real.log 2)))).sub
    ((tendsto_const_nhds : Tendsto (fun _ : Nat => (2 : ℝ)) atTop (𝓝 2)).mul hl)
  simp only [one_mul,mul_zero,sub_zero] at hc
  have ht := hp.atTop_mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) hc
  apply (Real.tendsto_exp_atTop.comp ht).congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hp0 := ne_of_gt (Real.rpow_pos_of_pos hnpos (7/8 : ℝ))
  change Real.exp ((n : ℝ)^(7/8 : ℝ)*
    (((vanishingLowBandWidth n : ℝ)/(n : ℝ)^(7/8 : ℝ))*Real.log 2-
      2*(Real.log (n : ℝ)/(n : ℝ)^(7/8 : ℝ)))) = _
  have he : (n : ℝ)^(7/8 : ℝ)*
    (((vanishingLowBandWidth n : ℝ)/(n : ℝ)^(7/8 : ℝ))*Real.log 2-
      2*(Real.log (n : ℝ)/(n : ℝ)^(7/8 : ℝ))) =
      (vanishingLowBandWidth n : ℝ)*Real.log 2-2*Real.log (n : ℝ) := by
    field_simp
  have hnexp : Real.exp (2*Real.log (n : ℝ)) = (n : ℝ)^2 := by
    rw [show (2 : ℝ)*Real.log (n : ℝ) = Real.log (n : ℝ)+Real.log (n : ℝ) by ring,
      Real.exp_add,Real.exp_log hnpos]
    ring
  rw [he,Real.exp_sub,hnexp,Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  simp only [sourceVanishingLowLower,Nat.cast_pow,Nat.cast_ofNat]

theorem sourceVanishingLowLower_eventually_quadratic :
    ∀ᶠ n : Nat in atTop, 8*((n+1 : Nat) : ℝ)^2 ≤ (sourceVanishingLowLower n : ℝ) := by
  filter_upwards [sourceVanishingLowLower_div_sq_tendsto_atTop.eventually_ge_atTop 32,
    eventually_ge_atTop 1] with n hb hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlarge := (le_div_iff₀ (sq_pos_of_pos hnpos)).mp hb
  have hsq := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (n : ℝ)+1) (by positivity : (0 : ℝ) ≤ 2*(n : ℝ))
  have hsmall : ((n : ℝ)+1)^2 ≤ (2*(n : ℝ))^2 := hsq.mpr (by linarith)
  push_cast
  nlinarith

end
end PowerLawSmallRAF
