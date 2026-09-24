import proofs.RandomViability.ProductiveSourceAsymptotics
import Mathlib.Data.Nat.Sqrt

namespace RandomViability
open Filter Topology
noncomputable section
set_option maxHeartbeats 50000

def productiveVolume (n : ℕ) : ℕ := 40+Nat.sqrt n

theorem productive_volume_ge (n : ℕ) : 40 ≤ productiveVolume n := by
  unfold productiveVolume
  omega

theorem productive_volume_sqrt_bound (n : ℕ) (hn : 1 ≤ n) :
    (productiveVolume n : ℝ) ≤ 41*Real.sqrt n := by
  have hs : (Nat.sqrt n : ℝ) ≤ Real.sqrt n :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' n)
  have h1 : (1 : ℝ) ≤ Real.sqrt n := Real.le_sqrt_of_sq_le (by exact_mod_cast hn)
  simp only [productiveVolume,Nat.cast_add,Nat.cast_ofNat]
  linarith

theorem productive_volume_tendsto : Tendsto productiveVolume atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with n hn
  have hb : b ≤ Nat.sqrt n := Nat.le_sqrt.mpr hn
  unfold productiveVolume
  omega

theorem productive_volume_div_nat :
    Tendsto (fun n => (productiveVolume n : ℝ)/(n : ℝ)) atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (41 : ℝ)) atTop (𝓝 41)).div_atTop hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hsR : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
    apply (div_le_div_iff₀ hnR hsR).mpr
    have hh := mul_le_mul_of_nonneg_right (productive_volume_sqrt_bound n hn) hsR.le
    nlinarith [Real.sq_sqrt hnR.le]

/-- The paid path costs O(V log V), which is negligible on the chosen
V(n)=40+isqrt(n) joint scale. -/
theorem productive_volume_log_div_nat :
    Tendsto (fun n => (productiveVolume n : ℝ)*Real.log (productiveVolume n)/(n : ℝ))
      atTop (𝓝 0) := by
  have hs := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hc := (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.log 41) atTop (𝓝 (Real.log 41))).div_atTop hs
  have hl : Tendsto (fun n : ℕ => Real.log (n : ℝ)/Real.sqrt n) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow,Function.comp_apply] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).tendsto_div_nhds_zero.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))
  have hu : Tendsto (fun n : ℕ => 41*(Real.log 41+Real.log (n : ℝ))/Real.sqrt n)
      atTop (𝓝 0) := by
    have ht := (hc.add hl).const_mul 41
    simp only [add_zero,mul_zero] at ht
    convert ht using 1
    funext n
    dsimp only [Function.comp_apply]
    ring
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · filter_upwards with n
    have hv : (1 : ℝ) ≤ productiveVolume n := by exact_mod_cast (show 1 ≤ productiveVolume n by have := productive_volume_ge n; omega)
    exact div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg hv)) (by positivity)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hs0 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn0
    have hv := productive_volume_sqrt_bound n hn
    have hv1 : (1 : ℝ) ≤ productiveVolume n := by exact_mod_cast (show 1 ≤ productiveVolume n by have := productive_volume_ge n; omega)
    have hsle : Real.sqrt (n : ℝ) ≤ n := (Real.sqrt_le_iff).mpr ⟨hn0.le,by nlinarith⟩
    have hvn : (productiveVolume n : ℝ) ≤ 41*(n : ℝ) := hv.trans (by linarith)
    have hlog : Real.log (productiveVolume n) ≤ Real.log 41+Real.log (n : ℝ) := by
      have hh := Real.log_le_log (by linarith : (0 : ℝ) < productiveVolume n) hvn
      rwa [Real.log_mul (by norm_num) hn0.ne'] at hh
    have hp := mul_le_mul hv hlog (Real.log_nonneg hv1) (by positivity : 0 ≤ 41*Real.sqrt (n : ℝ))
    calc
      _ ≤ (41*Real.sqrt (n : ℝ))*(Real.log 41+Real.log (n : ℝ))/(n : ℝ) :=
        div_le_div_of_nonneg_right hp hn0.le
      _ = (41*Real.sqrt (n : ℝ))*(Real.log 41+Real.log (n : ℝ))/(Real.sqrt (n : ℝ))^2 := by
        rw [Real.sq_sqrt hn0.le]
      _ = _ := by field_simp

end
end RandomViability
