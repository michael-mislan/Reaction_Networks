import proofs.FiniteCopyReactor.ExplicitScale
import proofs.FiniteCopyReactor.CycleHistory

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

/-- A deliberately simple inverse-volume envelope, useful for integer sizing. -/
theorem volume_times_error (V : ℝ) (hV : 200000000000 ≤ V) : V*oneCycleError V ≤ 5000000 := by
  have hv : 0 ≤ V := by linarith
  have he := mul_le_mul_of_nonneg_left (one_cycle_error_envelope V hv) hv
  have hx : (20:ℝ) ≤ V/10000000000 := by linarith
  have hx0 : 0 ≤ V/10000000000 := by positivity
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 20) hx 11) hx0
  have hp' : (20:ℝ)^11*(V/10000000000) ≤ (V/10000000000)^12 := by convert hp using 1
  have hseries := Real.pow_div_factorial_le_exp (V/10000000000) hx0 12
  norm_num [Nat.factorial] at hseries
  have hlin := (div_le_div_of_nonneg_right hp' (by norm_num : (0:ℝ) ≤ 479001600)).trans hseries
  norm_num at hlin
  have hs : V/40000 ≤ Real.exp (V/10000000000) := by linarith only [hlin,hv]
  have hs' := mul_le_mul_of_nonneg_right hs (Real.exp_pos (-(V/10000000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hs'
  have hy : (5000:ℝ) ≤ V/40000000 := by linarith
  have hy0 : 0 ≤ (V/40000000)^2 := sq_nonneg _
  have hq := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5000) hy 6) hy0
  have hq' : (5000:ℝ)^6*(V/40000000)^2 ≤ (V/40000000)^8 := by
    convert hq using 1
    ring
  have ht := Real.pow_div_factorial_le_exp (V/40000000) (by positivity) 8
  norm_num [Nat.factorial] at ht
  have ht' := (div_le_div_of_nonneg_right hq' (by norm_num : (0:ℝ) ≤ 40320)).trans ht
  norm_num at ht'
  have hf : 100*V*(V+1) ≤ Real.exp (V/40000000) := by nlinarith only [ht',hV]
  have hf' := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(V/40000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at hf'
  norm_num only [neg_div] at he hs' hf'
  nlinarith only [he,hs',hf']

def sufficientVolume (m : ℕ) (δ : ℝ) : ℕ := max 200000000000 ⌈5000000*(m:ℝ)/δ⌉₊

theorem sufficient_volume_error (m : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    (m:ℝ)*oneCycleError (sufficientVolume m δ) ≤ δ := by
  let V := sufficientVolume m δ
  have hVn : 200000000000 ≤ V := le_max_left _ _
  have hV : (200000000000:ℝ) ≤ V := by exact_mod_cast hVn
  have hv : 0 < (V:ℝ) := by linarith
  have hceil : ⌈5000000*(m:ℝ)/δ⌉₊ ≤ V := le_max_right _ _
  have hs : 5000000*(m:ℝ)/δ ≤ V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have hs' : 5000000*(m:ℝ) ≤ (V:ℝ)*δ := (div_le_iff₀ hδ).mp hs
  have hb := mul_le_mul_of_nonneg_left (volume_times_error V hV) (Nat.cast_nonneg (α := ℝ) m)
  change (m:ℝ)*oneCycleError (V:ℝ) ≤ δ
  have hprod : (V:ℝ)*((m:ℝ)*oneCycleError V) ≤ (V:ℝ)*δ := by nlinarith only [hb,hs']
  nlinarith only [hprod,hv]

theorem hundred_cycles_success (r d : ℝ) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : List (CycleObservation 200000000000) → Intervention)
    (N : Counts) (hN : Restart 200000000000 N) :
    99/100 ≤ cycleHistoryLaw 200000000000 r d (by norm_num) hr hr' hd hd'
      policy (fun _ => 1) 100 N hN [] := by
  have h := cycle_history_success_lower 200000000000 r d (by norm_num) (by norm_num)
    hr hr' hd hd' policy 100 N hN []
  norm_num only [Nat.cast_ofNat] at h
  linarith [hundred_cycle_error_budget]

end
end FiniteCopyReactor
