import proofs.InheritedCellAssay.PositiveMoments
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace InheritedCellAssay.PositiveMoments

noncomputable def horizonDays : ℝ := (100000/10001)*Real.log 2

theorem log_two_upper : Real.log 2 ≤ 7/10 := by
  have h := Real.sum_range_sub_log_div_le (x := (1/3 : ℝ)) (by norm_num) 3
  norm_num [Finset.sum_range_succ] at h
  have hh := (abs_le.mp h).2
  linarith

theorem horizon_bounds : horizonDays ∈ Set.Icc 0 7 := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h1 := log_two_upper
  unfold horizonDays
  constructor <;> linarith

theorem birth_horizon_bound : Real.exp ((1/10)*horizonDays) ≤ 2 := by
  have h0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have he := Real.exp_le_exp.mpr (show (1/10)*horizonDays ≤ Real.log 2 by
    unfold horizonDays
    linarith)
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he

theorem death_horizon_bound : Real.exp (-(3/10)*horizonDays) ≤ (1001/1000)*(1/8) := by
  let y : ℝ := (3/10001)*Real.log 2
  have hy : y ≤ 3/10001 := by
    dsimp [y]
    have := log_two_upper
    linarith
  have hlow := Real.add_one_le_exp (-y)
  have hp := mul_le_mul_of_nonneg_right hlow (Real.exp_nonneg y)
  have hcancel : Real.exp (-y)*Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at hp
  have he : Real.exp y ≤ 1001/1000 := by
    have hprod := mul_nonneg (show 0 ≤ 3/10001-y by linarith) (Real.exp_nonneg y)
    nlinarith
  have hbase : Real.exp (-3*Real.log 2) = 1/8 := by
    calc
      _ = Real.exp (-Real.log 2)*Real.exp (-Real.log 2)*Real.exp (-Real.log 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ = _ := by norm_num [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hsum : -(3/10)*horizonDays = -3*Real.log 2+y := by
    unfold horizonDays y
    ring
  rw [hsum, Real.exp_add, hbase]
  linarith

theorem endpoint_mean_upper (M : MomentODE) : M.S horizonDays+M.R horizonDays ≤ 11/20 := by
  have hs := sensitive_upper M horizonDays horizon_bounds.1
  have hr := resistant_upper M horizonDays horizon_bounds
  have hb := birth_horizon_bound
  have hd := death_horizon_bound
  linarith

end InheritedCellAssay.PositiveMoments
