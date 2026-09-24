import proofs.FiniteCopyReactor.SafeSourceCycle
import proofs.FiniteCopyReactor.SourcePulseMeasure

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy MeasureTheory
open scoped ENNReal BigOperators

theorem pulse_safe_source_lower (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (r d : ℝ) (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    ENNReal.ofReal (pulseCycle N V p hN r d hV hr hr' hd hd'
      (FiniteKernel.eventIndicator (realSafeEvent V))) ≤
      sourcePulseCycle N V p r d hV hr hd (countSafePayoff V) := by
  unfold pulseCycle sourcePulseCycle
  rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o)
    (joint_cycle_event_bounds V r d hV hr hr' hd hd' _ _ _).1)]
  apply Finset.sum_le_sum
  intro o _
  rw [ENNReal.ofReal_mul (pulseMass_nonneg N p o)]
  apply mul_le_mul_right
  have hh := joint_safe_source_lower V r d hV hr hr' hd hd'
    (postPulseBox N V p hN o,integerInitialCounters (doseU V p) (doseW V p))
  simpa only [integerCountState,postPulseBox_counts,pulseInitialState,
    realCounterState,integer_initial_counters_exact] using hh

/-- Joint returned-state, output and resource guarantee for the full pulse and unrestricted phases. -/
theorem actual_cycle_safe_bound (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    ENNReal.ofReal (1-oneCycleError V) ≤
      actualPulseCycleMeasure N V p r d hV (by linarith) hd {X | CountSafeCycleSuccess V X} := by
  have hh := (ENNReal.ofReal_le_ofReal (pulse_real_safe_bound N V p hN hlarge r d hV hr hr' hd hd')).trans
    (pulse_safe_source_lower N V p hN r d hV (by linarith) hr' hd hd')
  exact hh.trans_eq (actual_pulse_event N V p r d hV (by linarith) hd {X | CountSafeCycleSuccess V X})

theorem actual_cycle_success_bound (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    ENNReal.ofReal (1-oneCycleError V) ≤
      actualPulseCycleMeasure N V p r d hV (by linarith) hd {X | CountCycleSuccess V X} :=
  (actual_cycle_safe_bound N V p hN hlarge r d hV hr hr' hd hd').trans
    (measure_mono (fun _ h => h.2))

end
end FiniteCopyReactor
