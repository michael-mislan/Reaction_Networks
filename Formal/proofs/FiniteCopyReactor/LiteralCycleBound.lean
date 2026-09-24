import proofs.FiniteCopyReactor.ActualCycleBound
import proofs.FiniteCopyReactor.JointPhysicalEndpoint

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

/-- Full molecule pulse, three unmarked-output units, then one collection unit. -/
def literalPulseCycleMeasure (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) : Measure JointCounts :=
  (literalMarkedCycleKernel V r d hV hr hd).comap (pulseInitialState N V p)
    (measurable_of_countable _) ∘ₘ (pulsePMF N p).toMeasure

instance literalPulseCycleMeasure_probability (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    IsProbabilityMeasure (literalPulseCycleMeasure N V p r d hV hr hd) := by
  unfold literalPulseCycleMeasure
  infer_instance

theorem actual_cycle_measure_literal (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    actualPulseCycleMeasure N V p r d hV hr hd=literalPulseCycleMeasure N V p r d hV hr hd := by
  have hk : jointSourceCycleKernel V r d hV hr hd=literalMarkedCycleKernel V r d hV hr hd := by
    ext X A hA
    exact congrArg (fun μ : Measure JointCounts => μ A) (joint_source_cycle_kernel_literal V r d hV hr hd X)
  unfold actualPulseCycleMeasure literalPulseCycleMeasure
  rw [hk]

/-- Uniform one-cycle joint success for the literal source and every admitted pulse choice. -/
theorem literal_cycle_success_bound (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    ENNReal.ofReal (1-oneCycleError V) ≤
      literalPulseCycleMeasure N V p r d hV (by linarith) hd {X | CountCycleSuccess V X} := by
  rw [← actual_cycle_measure_literal]
  exact actual_cycle_success_bound N V p hN hlarge r d hV hr hr' hd hd'

end
end FiniteCopyReactor
