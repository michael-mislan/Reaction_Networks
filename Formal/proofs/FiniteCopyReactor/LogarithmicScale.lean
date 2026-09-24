import proofs.FiniteCopyReactor.Resolution

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal BigOperators

theorem residual_error_absorbed (V : ℝ) (hV : 200000000000 ≤ V) :
    1000000*(V+1)*Real.exp (-V/40000000) ≤ Real.exp (-V/10000000000) := by
  have hx : (4980:ℝ) ≤ 249*V/10000000000 := by linarith
  have hx0 : 0 ≤ 249*V/10000000000 := by linarith
  have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4980) hx 5) hx0
  have hp' : (4980:ℝ)^5*(249*V/10000000000) ≤ (249*V/10000000000)^6 := by
    convert hp using 1
  have ht := Real.pow_div_factorial_le_exp (249*V/10000000000) hx0 6
  norm_num [Nat.factorial] at ht
  have hb := (div_le_div_of_nonneg_right hp' (by norm_num : (0:ℝ) ≤ 720)).trans ht
  norm_num at hb
  have hf : 1000000*(V+1) ≤ Real.exp (249*V/10000000000) := by linarith only [hb,hV]
  have hf' := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-V/40000000)).le
  rw [← Real.exp_add] at hf'
  convert hf' using 1
  congr 1
  ring

theorem one_cycle_single_exponential (V : ℝ) (hV : 200000000000 ≤ V) :
    oneCycleError V ≤ 101*Real.exp (-V/10000000000) := by
  have h := one_cycle_error_envelope V (by linarith)
  linarith [residual_error_absorbed V hV]

def logarithmicVolume (m : ℕ) (δ : ℝ) : ℕ :=
  max 200000000000 ⌈10000000000*Real.log (101*(m:ℝ)/δ)⌉₊

theorem logarithmic_volume_error (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    (m:ℝ)*oneCycleError (logarithmicVolume m δ) ≤ δ := by
  let V := logarithmicVolume m δ
  have hVn : 200000000000 ≤ V := le_max_left _ _
  have hV : (200000000000:ℝ) ≤ V := by exact_mod_cast hVn
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have hceil : ⌈10000000000*Real.log (101*(m:ℝ)/δ)⌉₊ ≤ V := le_max_right _ _
  have hs : 10000000000*Real.log (101*(m:ℝ)/δ) ≤ V :=
    (Nat.le_ceil _).trans (by exact_mod_cast hceil)
  have he : 101*(m:ℝ)/δ ≤ Real.exp ((V:ℝ)/10000000000) := by
    rw [← Real.exp_log (by positivity : 0 < 101*(m:ℝ)/δ)]
    exact Real.exp_le_exp.mpr (by linarith)
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-((V:ℝ)/10000000000))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at he'
  have hd := mul_le_mul_of_nonneg_right he' hδ.le
  have hid : (101*(m:ℝ)/δ*Real.exp (-((V:ℝ)/10000000000)))*δ =
      101*(m:ℝ)*Real.exp (-((V:ℝ)/10000000000)) := by field_simp
  rw [hid] at hd
  have hb := mul_le_mul_of_nonneg_left (one_cycle_single_exponential V hV) hm'.le
  change (m:ℝ)*oneCycleError (V:ℝ) ≤ δ
  norm_num only [neg_div] at hb
  nlinarith only [hb,hd]

theorem exp_twenty_certificate : (484800000:ℝ) ≤ Real.exp 20 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 20) 37
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

theorem fixed_scale_error_sharp : oneCycleError (200000000000:ℝ) ≤ 1/4800000 := by
  have he := one_cycle_single_exponential (200000000000:ℝ) le_rfl
  have h := mul_le_mul_of_nonneg_right exp_twenty_certificate (Real.exp_pos (-20)).le
  rw [← Real.exp_add] at h
  norm_num at he h
  linarith

theorem mission_48000_budget : (48000:ℝ)*oneCycleError 200000000000 ≤ 1/100 := by
  linarith [fixed_scale_error_sharp]

theorem hundred_sharp_budget : (100:ℝ)*oneCycleError 200000000000 ≤ 21/1000000 := by
  linarith [fixed_scale_error_sharp]

end
end FiniteCopyReactor
