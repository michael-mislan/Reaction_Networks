import proofs.PowerLawSmallRAF.SourceLowBandAsymptotics
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

namespace PowerLawSmallRAF
open Filter Topology
noncomputable section
set_option maxHeartbeats 100000

theorem sourceLowBandIntegralLimit_lower : (73/50 : ℝ) ≤ sourceLowBandIntegralLimit := by
  have hlog0 : 0 ≤ Real.log 2 := by positivity
  have hlog1 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hfour : Real.exp (2*Real.log 2) = 4 := by
    rw [show (2 : ℝ)*Real.log 2 = Real.log 2+Real.log 2 by ring, Real.exp_add]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hfull : criticalPartialMass (-2) (Real.log 2) = 3/2 := by
    rw [criticalPartialMass, integral_exp_neg_mul (-2) (by norm_num)]
    simp only [neg_neg]
    rw [hfour]
    norm_num
  have hshort : criticalPartialMass (-2) (Real.log 2/100) ≤ 4*(Real.log 2/100) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := Real.log 2/100) (C := (4 : ℝ))
      (f := fun x : ℝ => Real.exp (-(-2 : ℝ)*x)) (by
        intro x hx
        rw [Set.uIoc_of_le (by positivity)] at hx
        simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [← hfour]
        apply Real.exp_le_exp.mpr
        nlinarith only [hx.2, hlog0])
    have hnorm' : |criticalPartialMass (-2) (Real.log 2/100)| ≤ 4*(Real.log 2/100) := by
      simpa only [criticalPartialMass, Real.norm_eq_abs, sub_zero,
        abs_of_nonneg (by positivity : 0 ≤ Real.log 2/100)] using hnorm
    exact (le_abs_self _).trans hnorm'
  unfold sourceLowBandIntegralLimit
  rw [hfull]
  linarith

theorem sourceLowBand_retained_budget :
    ∀ᶠ n : Nat in atTop, (4/5 : ℝ) ≤ (49/50 : ℝ)*(19/20 : ℝ)*
      ((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceLowBandMean n := by
  have hmargin : (4/5 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
      (sourceLowBandIntegralLimit/(Real.pi^2/6)) := by
    have hp : Real.pi^2 < (3.15 : ℝ)^2 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
    rw [← mul_div_assoc, lt_div_iff₀ (by positivity)]
    nlinarith [sourceLowBandIntegralLimit_lower]
  have h := ((tendsto_const_nhds : Tendsto (fun _ : Nat => (49/50 : ℝ)*(19/20 : ℝ))
    atTop (𝓝 ((49/50 : ℝ)*(19/20 : ℝ)))).mul sourceLowBandDensity_tendsto)
      (Ioi_mem_nhds hmargin)
  filter_upwards [h] with n hn
  change (4/5 : ℝ) < (49/50 : ℝ)*(19/20 : ℝ)*
    (((sourceMoleculeCount n : ℝ)/(sourceReactionCount n : ℝ))*sourceLowBandMean n) at hn
  nlinarith only [hn.le]

end
end PowerLawSmallRAF
