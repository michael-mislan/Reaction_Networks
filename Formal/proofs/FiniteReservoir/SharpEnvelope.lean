import proofs.FiniteReservoir.SharpPhaseCycle
import proofs.FiniteReservoir.ErrorScale

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

/-- Every term other than the phase term is a bounded multiple of `exp(-V/40000000)`. -/
theorem sharp_error_envelope (V : ℝ) (hV : 0 ≤ V) :
    sharpBothError V ≤ 100*Real.exp (-phaseRate*V)+2000000*(V+1)*Real.exp (-V/40000000) := by
  let T := Real.exp (-V/40000000)
  have ht : 0 ≤ T := (Real.exp_pos _).le
  have hd (D : ℝ) (hD : 0 < D) (hD' : D ≤ 40000000) : Real.exp (-V/D) ≤ T := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_left hV hD hD'
    simpa only [neg_div] using neg_le_neg h
  have hc (c : ℝ) (hc : 1/40000000 ≤ c) : Real.exp (-c*V) ≤ T := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_right hc hV
    linarith
  have he2 : Real.exp (1/50:ℝ) ≤ 2 := by
    have h := exp_small_quadratic (1/50:ℝ) (by norm_num)
    linarith
  have ho (D a : ℝ) (hD : 0 < D) (hD' : D ≤ 40000000) (ha : a ≤ 1/50) :
      Real.exp (-V/D+a) ≤ 2*T := by
    rw [Real.exp_add]
    have h := mul_le_mul (hd D hD hD') ((Real.exp_le_exp.mpr ha).trans he2) (Real.exp_pos _).le ht
    simpa only [mul_comm] using h
  have hV0 := mul_le_mul_of_nonneg_left (ho 2000 (1/50) (by norm_num) (by norm_num) le_rfl) hV
  have hV1 := mul_le_mul_of_nonneg_left (ho 10000 (9/500) (by norm_num) (by norm_num) (by norm_num)) hV
  have hVT := mul_nonneg hV ht
  have h0 := hc (1177/1000000000) (by norm_num)
  have h1 := hc (3/5000000) (by norm_num)
  have h2 := hd 100000 (by norm_num) (by norm_num)
  have h3 := hd 1 (by norm_num) (by norm_num)
  have h4 := hd 200 (by norm_num) (by norm_num)
  have h5 := hd 300 (by norm_num) (by norm_num)
  have h6 := hd 2000 (by norm_num) (by norm_num)
  have h7 := hd 2 (by norm_num) (by norm_num)
  have h8 := hd 10000 (by norm_num) (by norm_num)
  have h9 := hd 320000 (by norm_num) (by norm_num)
  have h10 := hd 40000000 (by norm_num) (by norm_num)
  unfold sharpBothError sharpOneCycleError sharpPreparedError sharpJointCounterError stateRestartError
    sharpFreeCollectionError sharpFreeDiscreteError collectionResidenceError materialExitError
  change _ ≤ 100*Real.exp (-phaseRate*V)+2000000*(V+1)*T
  norm_num only [div_one] at h3
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,hV0,hV1,hVT,ht]

/-- The residual is absorbed by the phase term from `V = 10^10` on, twenty times
below the floor that the rounded exponent needs. -/
theorem sharp_residual_absorbed (V : ℝ) (hV : 10000000000 ≤ V) :
    2000000*(V+1)*Real.exp (-V/40000000) ≤ Real.exp (-phaseRate*V) := by
  have hc : (0:ℝ) < 216911/8750000000000 := by norm_num
  have hx : (247:ℝ) ≤ 216911/8750000000000*V := by
    have h := mul_le_mul_of_nonneg_left hV hc.le
    linarith
  have hx0 : 0 ≤ 216911/8750000000000*V := by linarith
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 247) hx 9) hx0
  have hp' : (247:ℝ)^9*(216911/8750000000000*V) ≤ (216911/8750000000000*V)^10 := by
    convert hp using 1
  have ht := Real.pow_div_factorial_le_exp (216911/8750000000000*V) hx0 10
  norm_num [Nat.factorial] at ht hp'
  have hb := (div_le_div_of_nonneg_right hp' (by norm_num : (0:ℝ) ≤ 3628800)).trans ht
  norm_num at hb
  have hf : 2000000*(V+1) ≤ Real.exp (216911/8750000000000*V) := by
    nlinarith only [hb,hV]
  have hf' := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-V/40000000)).le
  rw [← Real.exp_add] at hf'
  have hid : 216911/8750000000000*V+-V/40000000 = -phaseRate*V := by
    unfold phaseRate
    ring
  rw [hid] at hf'
  exact hf'

theorem sharp_single_exponential (V : ℝ) (hV : 10000000000 ≤ V) :
    sharpBothError V ≤ 101*Real.exp (-phaseRate*V) := by
  have h := sharp_error_envelope V (by linarith)
  linarith [sharp_residual_absorbed V hV]

theorem sharpOneCycleError_le_both (V : ℝ) : sharpOneCycleError V ≤ sharpBothError V := by
  unfold sharpBothError
  linarith [(Real.exp_pos (-V/2000)).le]

theorem sharp_one_cycle_single_exponential (V : ℝ) (hV : 10000000000 ≤ V) :
    sharpOneCycleError V ≤ 101*Real.exp (-phaseRate*V) :=
  (sharpOneCycleError_le_both V).trans (sharp_single_exponential V hV)

theorem sharpBothError_nonneg (V : ℕ) : 0 ≤ sharpBothError V := by
  unfold sharpBothError sharpOneCycleError
  have := sharpPreparedError_nonneg V
  positivity

theorem exp_ten_certificate : (10100:ℝ) ≤ Real.exp 10 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 10) 20
  norm_num [Finset.sum_range_succ,Nat.factorial] at h
  linarith

/-- Useful confidence needs a floor; the rounded certificate needed `2*10^11`. -/
theorem sharp_error_small (V : ℝ) (hV : 50000000000 ≤ V) : sharpBothError V ≤ 1/100 := by
  have hs := sharp_single_exponential V (by linarith)
  have hx : (10:ℝ) ≤ phaseRate*V := by
    unfold phaseRate
    nlinarith
  have hn : Real.exp (-phaseRate*V) ≤ Real.exp (-10) :=
    Real.exp_le_exp.mpr (by linarith)
  have h10 : Real.exp (-(10:ℝ)) ≤ 1/10100 := by
    rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos 10) (by norm_num)]
    linarith [exp_ten_certificate]
  have hne : Real.exp (-phaseRate*V) = Real.exp (-(phaseRate*V)) := by
    congr 1
    ring
  rw [hne] at hn
  linarith

/-- Sufficient copy scale at the unrounded phase rate. -/
def sharpVolume (m : ℕ) (δ : ℝ) : ℕ :=
  max 50000000000 ⌈Real.log (101*(m:ℝ)/δ)/phaseRate⌉₊

theorem sharp_volume_scale (m : ℕ) (δ : ℝ) : 50000000000 ≤ sharpVolume m δ := le_max_left _ _

theorem sharp_confidence_budget (V m : ℕ) (hm : 0 < m) (δ : ℝ) (hd : 0 < δ)
    (hscale : 10000000000 ≤ V) (hlog : Real.log (101*(m:ℝ)/δ)/phaseRate ≤ V) :
    (m:ℝ)*sharpBothError V ≤ δ := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hr : (0:ℝ) < phaseRate := by unfold phaseRate; norm_num
  have hlog' : Real.log (101*(m:ℝ)/δ) ≤ phaseRate*(V:ℝ) := by
    have := (div_le_iff₀ hr).mp hlog
    linarith
  have he : 101*(m:ℝ)/δ ≤ Real.exp (phaseRate*(V:ℝ)) := by
    rw [← Real.exp_log (by positivity : 0 < 101*(m:ℝ)/δ)]
    exact Real.exp_le_exp.mpr hlog'
  have he' := mul_le_mul_of_nonneg_right he (Real.exp_pos (-(phaseRate*(V:ℝ)))).le
  rw [← Real.exp_add,add_neg_cancel,Real.exp_zero] at he'
  have hh := mul_le_mul_of_nonneg_right he' hd.le
  have hid : (101*(m:ℝ)/δ*Real.exp (-(phaseRate*(V:ℝ))))*δ=
      101*(m:ℝ)*Real.exp (-(phaseRate*(V:ℝ))) := by field_simp
  rw [hid] at hh
  have hb := mul_le_mul_of_nonneg_left
    (sharp_single_exponential V (by exact_mod_cast hscale)) hm'.le
  have hne : Real.exp (-phaseRate*(V:ℝ)) = Real.exp (-(phaseRate*(V:ℝ))) := by
    congr 1
    ring
  rw [hne] at hb
  nlinarith only [hb,hh]

theorem sharp_volume_budget (m : ℕ) (hm : 0 < m) (δ : ℝ) (hd : 0 < δ) :
    (m:ℝ)*sharpBothError (sharpVolume m δ) ≤ δ := by
  apply sharp_confidence_budget _ m hm δ hd
    (le_trans (by norm_num) (sharp_volume_scale m δ))
  have hc : ⌈Real.log (101*(m:ℝ)/δ)/phaseRate⌉₊ ≤ sharpVolume m δ := le_max_right _ _
  exact (Nat.le_ceil _).trans (by exact_mod_cast hc)

/-- The improved hundred-cycle certificate: the confidence of the original
example at `V = 2*10^11`, now already at `V = 9.6*10^10`. -/
theorem sharp_hundred_budget : (100:ℝ)*sharpBothError 96000000000 ≤ 21/1000000 := by
  have hs := sharp_single_exponential 96000000000 (by norm_num)
  have hx : (20:ℝ) ≤ phaseRate*96000000000 := by unfold phaseRate; norm_num
  have hn : Real.exp (-phaseRate*96000000000) ≤ Real.exp (-20) :=
    Real.exp_le_exp.mpr (by linarith)
  have h20 : Real.exp (-(20:ℝ)) ≤ 1/484800000 := by
    rw [Real.exp_neg,inv_le_comm₀ (Real.exp_pos 20) (by norm_num)]
    linarith [FiniteCopyReactor.exp_twenty_certificate]
  have hne : Real.exp (-phaseRate*96000000000) = Real.exp (-(phaseRate*96000000000)) := by
    congr 1
    ring
  linarith

end
end FiniteReservoir
