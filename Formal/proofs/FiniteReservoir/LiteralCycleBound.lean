import proofs.FiniteReservoir.ActualCycleBound
import proofs.FiniteReservoir.JointPhysicalEndpoint

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

/-- Full molecule pulse, three unmarked-output units, then one collection unit. -/
def literalPulseCycleMeasure (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M) (fuel : FuelState M)
    (hV : 0 < (V:ℝ))  : Measure (JointCounts M) :=
  (literalMarkedCycleKernel V M params hV).comap (pulseInitialState N V M p fuel)
    (measurable_of_countable _) ∘ₘ (pulsePMF N p).toMeasure

instance literalPulseCycleMeasure_probability (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M) (fuel : FuelState M)
    (hV : 0 < (V:ℝ))  :
    IsProbabilityMeasure (literalPulseCycleMeasure N V M p params fuel hV) := by
  unfold literalPulseCycleMeasure
  infer_instance

theorem actual_cycle_measure_literal (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M) (fuel : FuelState M)
    (hV : 0 < (V:ℝ))  :
    actualPulseCycleMeasure N V M p params fuel hV=literalPulseCycleMeasure N V M p params fuel hV := by
  have hk : jointSourceCycleKernel V M params hV=literalMarkedCycleKernel V M params hV := by
    ext X A hA
    exact congrArg (fun μ : Measure (JointCounts M) => μ A) (joint_source_cycle_kernel_literal V M params hV X)
  unfold actualPulseCycleMeasure literalPulseCycleMeasure
  rw [hk]

/-- Uniform one-cycle joint success for the literal source and every admitted pulse choice. -/
theorem literal_cycle_success_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))
     :
    ENNReal.ofReal (1-oneCycleError V) ≤
      literalPulseCycleMeasure N V M p params fuel hV {X | CountCycleSuccess V M X} := by
  rw [← actual_cycle_measure_literal]
  exact actual_cycle_success_bound N V M p hN hlarge params fuel hV

end
end FiniteReservoir
