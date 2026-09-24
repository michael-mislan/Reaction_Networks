import proofs.FiniteReservoir.PhysicalHistory

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

abbrev ReturnedHistory (M : ℕ) := List (JointCounts M)

instance returnedHistory_measurableSpace (M : ℕ) : MeasurableSpace (ReturnedHistory M) := ⊤
instance returnedHistory_measurableSingleton (M : ℕ) : MeasurableSingletonClass (ReturnedHistory M) := ⟨fun _ => trivial⟩

def returnedObservation {M : ℕ} (N : CountState M) (h : (ReturnedHistory M)) : (JointCounts M) := h.headD (N,fun _ => 0)

/-- Each sampled outcome is prepended to the existing history; no reset state is substituted. -/
def returnedHistoryStep (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention) :
    Kernel (ReturnedHistory M) (ReturnedHistory M) := Kernel.ofFunOfCountable (fun h =>
      (literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params (returnedObservation N h).1.2 hV).map (fun X => X::h))

instance returnedHistoryStep_markov (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention) :
    IsMarkovKernel (returnedHistoryStep M N V params hV policy) := by
  constructor
  intro h
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem returned_history_conditional_law (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention) (h : (ReturnedHistory M)) :
    ((returnedHistoryStep M N V params hV policy) h).map (returnedObservation N)=
      literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params (returnedObservation N h).1.2 hV := by
  change ((literalPulseCycleMeasure (returnedObservation N h).1.1 V M (policy h) params (returnedObservation N h).1.2 hV).map
    (fun X => X::h)).map (returnedObservation N)=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : (returnedObservation N ∘ fun X : (JointCounts M) => X::h)=id := by
    funext X
    rfl
  rw [he,Measure.map_id]

def returnedPhysicalHistory (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ))  (policy : (ReturnedHistory M) → Intervention) :
    PhysicalHistory (ReturnedHistory M) V M params hV where
  current h := (returnedObservation N h).1
  observe := returnedObservation N
  observe_measurable := measurable_of_countable _
  current_return _ := rfl
  policy := policy
  step := returnedHistoryStep M N V params hV policy
  markov := inferInstance
  conditional_law := returned_history_conditional_law M N V params hV policy

theorem returned_history_success_lower (M : ℕ) (N : CountState M) (V : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) 
    (policy : (ReturnedHistory M) → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N.1) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      successfulHistoryKernel (returnedHistoryStep M N V params hV policy)
        (physicalHistorySuccess (returnedPhysicalHistory M N V params hV policy))
        (physical_history_success_measurable _) n [] Set.univ :=
  physical_history_success_lower (returnedPhysicalHistory M N V params hV policy)
    hscale n [] hN

end
end FiniteReservoir
