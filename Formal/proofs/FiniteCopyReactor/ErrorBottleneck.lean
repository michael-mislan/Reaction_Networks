import proofs.FiniteCopyReactor.ErrorEnvelope

namespace FiniteCopyReactor
noncomputable section

/-- The phase-occupation term is an unavoidable summand of this particular error certificate. -/
theorem one_cycle_error_phase_lower (V : ℝ) (hV : 0 ≤ V) :
    100*Real.exp (-V/10000000000) ≤ oneCycleError V := by
  have hh : 0 ≤ oneCycleError V-100*Real.exp (-V/10000000000) := by
    unfold oneCycleError preparedCycleError jointCounterError stateRestartError freeCollectionError
      freeDiscreteError collectionResidenceError materialExitError
    ring_nf
    positivity
  linarith

/-- This is a lower limit for the current analytic certificate, not for a physical reactor. -/
theorem error_certificate_volume_limit (V δ : ℝ) (m : ℕ) (hV : 0 ≤ V) (hδ : 0 < δ)
    (hm : 0 < m) (hbudget : (m:ℝ)*oneCycleError V ≤ δ) :
    10000000000*Real.log (100*(m:ℝ)/δ) ≤ V := by
  have hmr : (0:ℝ) < m := by exact_mod_cast hm
  have hp : (0:ℝ) < 100*(m:ℝ) := by positivity
  have hlo := mul_le_mul_of_nonneg_left (one_cycle_error_phase_lower V hV) hmr.le
  have he : Real.exp (-V/10000000000) ≤ δ/(100*(m:ℝ)) := by
    apply (le_div_iff₀ hp).mpr
    nlinarith
  have hl := Real.log_le_log (Real.exp_pos _) he
  rw [Real.log_exp,Real.log_div (ne_of_gt hδ) (ne_of_gt hp)] at hl
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hδ)]
  linarith

end
end FiniteCopyReactor
