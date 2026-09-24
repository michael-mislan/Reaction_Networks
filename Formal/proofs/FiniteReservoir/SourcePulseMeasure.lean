import proofs.FiniteReservoir.SourceCycleMeasure
import proofs.FiniteReservoir.PulseCycle
import proofs.FiniteCopyReactor.SourcePulseMeasure

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding FiniteCopyReactor
open scoped ENNReal BigOperators

def pulseInitialState (N : Counts) (V M : ℕ) (p : Intervention) (fuel : FuelState M)
    (o : PulseOutcome N) : JointCounts M :=
  ((postPulseCounts N V p o,fuel),integerInitialCounters (doseU V p) (doseW V p))

/-- Every pulse outcome is retained, with exactly the incoming bath. -/
def actualPulseCycleMeasure (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M)
    (fuel : FuelState M) (hV : 0 < (V:ℝ)) : Measure (JointCounts M) :=
  (jointSourceCycleKernel V M params hV).comap (pulseInitialState N V M p fuel)
    (measurable_of_countable _) ∘ₘ (pulsePMF N p).toMeasure

instance actualPulseCycleMeasure_probability (N : Counts) (V M : ℕ) (p : Intervention)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    IsProbabilityMeasure (actualPulseCycleMeasure N V M p params fuel hV) := by
  unfold actualPulseCycleMeasure
  infer_instance

def sourcePulseCycle (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M)
    (fuel : FuelState M) (hV : 0 < (V:ℝ)) (f : JointCounts M → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ o,ENNReal.ofReal (pulseMass N p o)*jointSourceCycle V M params hV f (pulseInitialState N V M p fuel o)

theorem actual_pulse_expectation (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M)
    (fuel : FuelState M) (hV : 0 < (V:ℝ)) (f : JointCounts M → ℝ≥0∞) :
    (∫⁻ X,f X ∂actualPulseCycleMeasure N V M p params fuel hV)=sourcePulseCycle N V M p params fuel hV f := by
  unfold actualPulseCycleMeasure
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) (measurable_of_countable f).aemeasurable,lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),pulsePMF,PMF.ofFintype_apply]
  apply Finset.sum_congr rfl
  intro o _
  change (∫⁻ X,f X ∂jointSourceCycleKernel V M params hV (pulseInitialState N V M p fuel o))*
    ENNReal.ofReal (pulseMass N p o)=_
  rw [← joint_source_cycle_kernel]
  exact mul_comm _ _

theorem actual_pulse_event (N : Counts) (V M : ℕ) (p : Intervention) (params : Parameters M)
    (fuel : FuelState M) (hV : 0 < (V:ℝ)) (A : Set (JointCounts M)) :
    sourcePulseCycle N V M p params fuel hV (fun X => if X ∈ A then 1 else 0)=
      actualPulseCycleMeasure N V M p params fuel hV A := by
  rw [← actual_pulse_expectation]
  exact lintegral_indicator_one (Set.to_countable A).measurableSet

end
end FiniteReservoir
