import proofs.FiniteCopyReactor.ErrorEnvelope

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem one_cycle_error_small (V : ℝ) (hV : 200000000000 ≤ V) : oneCycleError V ≤ 1/10000 := by
  have hv : 0 ≤ V := by linarith
  have he := one_cycle_error_envelope V hv
  have h20 : (5000000:ℝ) ≤ Real.exp 20 := by
    have h := Real.pow_div_factorial_le_exp 20 (show (0:ℝ) ≤ 20 by norm_num) 12
    norm_num [Nat.factorial] at h
    linarith
  have hs : (5000000:ℝ) ≤ Real.exp (V/10000000000) :=
    h20.trans (Real.exp_le_exp.mpr (by linarith))
  have hs' := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(V/10000000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hs'
  have hx : (5000:ℝ) ≤ V/40000000 := by linarith
  have hx0 : 0 ≤ V/40000000 := by positivity
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5000) hx 7) hx0
  have hp' : (5000:ℝ)^7*(V/40000000) ≤ (V/40000000)^8 := by
    convert hp using 1
  have hxexp := Real.pow_div_factorial_le_exp (V/40000000) hx0 8
  norm_num [Nat.factorial] at hxexp
  have hlin := (div_le_div_of_nonneg_right hp' (by norm_num : (0:ℝ) ≤ 40320)).trans hxexp
  norm_num at hlin
  have hf : 10000000000000*(V+1) ≤ Real.exp (V/40000000) := by nlinarith only [hlin,hV]
  have hf' := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(V/40000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hf'
  norm_num only [neg_div] at he hs' hf'
  linarith only [he,hs',hf']

theorem explicit_restart_witness : ∃ N, Restart 200000000000 N := by
  convert restart_nonempty 200000000 using 1

theorem hundred_cycle_error_budget : 100*oneCycleError (200000000000:ℝ) ≤ 1/100 := by
  have h := one_cycle_error_small (200000000000:ℝ) le_rfl
  linarith

end
end FiniteCopyReactor
