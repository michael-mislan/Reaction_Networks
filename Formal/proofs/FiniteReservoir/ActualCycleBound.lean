import proofs.FiniteReservoir.SafeSourceCycle
import proofs.FiniteReservoir.SourcePulseMeasure

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy MeasureTheory FiniteCopyReactor
open scoped ENNReal BigOperators

theorem pulse_safe_source_lower (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    ENNReal.ofReal (pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (realSafeEvent V M))) ≤
      sourcePulseCycle N V M p params fuel hV (countSafePayoff V M) := by
  unfold pulseCycle sourcePulseCycle
  rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o)
    (joint_cycle_event_bounds V M params hV _ _ _).1)]
  apply Finset.sum_le_sum
  intro o _
  rw [ENNReal.ofReal_mul (pulseMass_nonneg N p o)]
  apply mul_le_mul_right
  have hh := joint_safe_source_lower V M params hV
    (postPulse N V M p hN fuel o,integerInitialCounters (doseU V p) (doseW V p))
  simpa only [integerCountState,postPulse,postPulseBox_counts,pulseInitialState,
    realCounterState,integer_initial_counters_exact] using hh

/-- Full-pulse physical guarantee, uniformly over the incoming finite bath. -/
theorem actual_cycle_safe_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    ENNReal.ofReal (1-oneCycleError V) ≤
      actualPulseCycleMeasure N V M p params fuel hV {X | CountSafeCycleSuccess V M X} := by
  have hh := (ENNReal.ofReal_le_ofReal (pulse_real_safe_bound N V M p hN hlarge params fuel hV)).trans
    (pulse_safe_source_lower N V M p hN params fuel hV)
  exact hh.trans_eq (actual_pulse_event N V M p params fuel hV {X | CountSafeCycleSuccess V M X})

theorem actual_cycle_success_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    ENNReal.ofReal (1-oneCycleError V) ≤
      actualPulseCycleMeasure N V M p params fuel hV {X | CountCycleSuccess V M X} :=
  (actual_cycle_safe_bound N V M p hN hlarge params fuel hV).trans
    (measure_mono (fun _ h => h.2))

end
end FiniteReservoir
