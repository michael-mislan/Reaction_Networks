import proofs.FiniteCopyReactor.PulseCycle

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem oneCycleError_nonneg (V : ℕ) : 0 ≤ oneCycleError V := by
  unfold oneCycleError
  exact add_nonneg (add_nonneg (Real.exp_pos _).le (by positivity)) (preparedCycleError_nonneg V)

theorem one_cycle_error_envelope (V : ℝ) (hV : 0 ≤ V) :
    oneCycleError V ≤ 100*Real.exp (-V/10000000000)+1000000*(V+1)*Real.exp (-V/40000000) := by
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
  unfold oneCycleError preparedCycleError jointCounterError stateRestartError freeCollectionError freeDiscreteError
    collectionResidenceError materialExitError
  change _ ≤ 100*Real.exp (-V/10000000000)+1000000*(V+1)*T
  norm_num only [div_one] at h3
  linarith only [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,hV0,hV1,hVT,ht]

end
end FiniteCopyReactor
