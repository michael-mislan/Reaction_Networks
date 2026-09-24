import proofs.FiniteCopyReactor.SourceCycleMeasure
import proofs.FiniteCopyReactor.PulseCycle

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal BigOperators

def pulsePMF (N : Counts) (p : Intervention) : PMF (PulseOutcome N) :=
  PMF.ofFintype (fun o => ENNReal.ofReal (pulseMass N p o)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun o _ => pulseMass_nonneg N p o),pulseMass_total,ENNReal.ofReal_one])

def pulseInitialState (N : Counts) (V : ℕ) (p : Intervention) (o : PulseOutcome N) : JointCounts :=
  (postPulseCounts N V p o,integerInitialCounters (doseU V p) (doseW V p))

/-- All pulse outcomes feed the unrestricted chronological phases; there is no conditioning on success. -/
def actualPulseCycleMeasure (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) : Measure JointCounts :=
  (jointSourceCycleKernel V r d hV hr hd).comap (pulseInitialState N V p)
    (measurable_of_countable _) ∘ₘ (pulsePMF N p).toMeasure

instance actualPulseCycleMeasure_probability (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) :
    IsProbabilityMeasure (actualPulseCycleMeasure N V p r d hV hr hd) := by
  unfold actualPulseCycleMeasure
  infer_instance

def sourcePulseCycle (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (f : JointCounts → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ o,ENNReal.ofReal (pulseMass N p o)*jointSourceCycle V r d hV hr hd f (pulseInitialState N V p o)

theorem actual_pulse_expectation (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (f : JointCounts → ℝ≥0∞) :
    (∫⁻ X,f X ∂actualPulseCycleMeasure N V p r d hV hr hd)=sourcePulseCycle N V p r d hV hr hd f := by
  unfold actualPulseCycleMeasure
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) (measurable_of_countable f).aemeasurable,lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),pulsePMF,PMF.ofFintype_apply]
  apply Finset.sum_congr rfl
  intro o _
  change (∫⁻ X,f X ∂jointSourceCycleKernel V r d hV hr hd (pulseInitialState N V p o))*
    ENNReal.ofReal (pulseMass N p o)=_
  rw [← joint_source_cycle_kernel]
  exact mul_comm _ _

theorem actual_pulse_event (N : Counts) (V : ℕ) (p : Intervention) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (A : Set JointCounts) :
    sourcePulseCycle N V p r d hV hr hd (fun X => if X ∈ A then 1 else 0)=
      actualPulseCycleMeasure N V p r d hV hr hd A := by
  rw [← actual_pulse_expectation]
  exact lintegral_indicator_one (Set.to_countable A).measurableSet

end
end FiniteCopyReactor
