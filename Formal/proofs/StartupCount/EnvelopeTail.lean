import proofs.StartupCount.AffineRenewal
import Mathlib.Analysis.SpecialFunctions.Exp

namespace StartupCount
open Classical
noncomputable section
set_option maxHeartbeats 40000

theorem exp_neg_one_le_nine_tenths : Real.exp (-1) ≤ (9/10 : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have hh := Real.add_one_le_exp (1 : ℝ)
    linarith
  rw [Real.exp_neg]
  have hp := Real.exp_pos (1 : ℝ)
  rw [← one_div]
  apply (div_le_iff₀ hp).mpr
  linarith

theorem exp_startup_power_bound (c t : ℝ) (m : ℕ) (hc : (m : ℝ) ≤ c) (ht : 1 ≤ t) :
    Real.exp (-c*t) ≤ (9/10 : ℝ)^m := by
  have hc0 : 0 ≤ c := (Nat.cast_nonneg m).trans hc
  have hct : (m : ℝ) ≤ c*t := by nlinarith
  calc
    _ ≤ Real.exp ((m : ℝ)*(-1)) := Real.exp_le_exp.mpr (by linarith)
    _ = (Real.exp (-1))^m := Real.exp_nat_mul (-1) m
    _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le exp_neg_one_le_nine_tenths m

theorem affine_source_envelope_le (V t : ℝ) (hV : 0 < V) (ht : 1 ≤ t) (m K : ℕ)
    (hm : (m : ℝ) ≤ V/2000000000000000000) :
    affineEnvelope (V/100000000000000000)
      (((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/(V/100000000000000000))
      ((9/10 : ℝ)^K) t ≤ 10*(9/10 : ℝ)^m := by
  let c := V/100000000000000000
  have hc : 0 < c := by dsimp [c]; positivity
  have hmc : 20*(m : ℝ) ≤ c := by dsimp [c]; linarith
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have he := exp_startup_power_bound c t m (by linarith) ht
  have he0 : 0 ≤ Real.exp (-c*t) := (Real.exp_pos _).le
  have hK : (9/10 : ℝ)^K ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hqm : 0 ≤ (9/10 : ℝ)^m := by positivity
  have hb : ((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/c ≤ 9*(9/10 : ℝ)^m := by
    apply (div_le_iff₀ hc).mpr
    have hh := mul_le_mul_of_nonneg_right (show (1558/9)*(m : ℝ) ≤ 9*c by linarith) hqm
    nlinarith only [hh]
  have hb0 : 0 ≤ ((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/c := by positivity
  have hf := mul_le_mul_of_nonneg_left hK he0
  have hfb := mul_le_mul_of_nonneg_right (show 1-Real.exp (-c*t) ≤ 1 by linarith) hb0
  change Real.exp (-c*t)*(9/10 : ℝ)^K+
    (1-Real.exp (-c*t))*(((1558/9)*(m : ℝ)*(9/10 : ℝ)^m)/c) ≤ _
  nlinarith only [he,hb,hf,hfb]

end
end StartupCount
