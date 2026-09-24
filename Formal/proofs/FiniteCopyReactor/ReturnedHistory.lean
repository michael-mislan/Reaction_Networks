import proofs.FiniteCopyReactor.PhysicalHistory

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

abbrev ReturnedHistory := List JointCounts

instance returnedHistory_measurableSpace : MeasurableSpace ReturnedHistory := ⊤
instance returnedHistory_measurableSingleton : MeasurableSingletonClass ReturnedHistory := ⟨fun _ => trivial⟩

def returnedObservation (N : Counts) (h : ReturnedHistory) : JointCounts := h.headD (N,fun _ => 0)

/-- Each sampled outcome is prepended to the existing history; no reset state is substituted. -/
def returnedHistoryStep (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention) :
    Kernel ReturnedHistory ReturnedHistory := Kernel.ofFunOfCountable (fun h =>
      (literalPulseCycleMeasure (returnedObservation N h).1 V (policy h) r d hV hr hd).map (fun X => X::h))

instance returnedHistoryStep_markov (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention) :
    IsMarkovKernel (returnedHistoryStep N V r d hV hr hd policy) := by
  constructor
  intro h
  exact Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable

theorem returned_history_conditional_law (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention) (h : ReturnedHistory) :
    ((returnedHistoryStep N V r d hV hr hd policy) h).map (returnedObservation N)=
      literalPulseCycleMeasure (returnedObservation N h).1 V (policy h) r d hV hr hd := by
  change ((literalPulseCycleMeasure (returnedObservation N h).1 V (policy h) r d hV hr hd).map
    (fun X => X::h)).map (returnedObservation N)=_
  rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  have he : (returnedObservation N ∘ fun X : JointCounts => X::h)=id := by
    funext X
    rfl
  rw [he,Measure.map_id]

def returnedPhysicalHistory (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) (policy : ReturnedHistory → Intervention) :
    PhysicalHistory ReturnedHistory V r d hV hr hd where
  current h := (returnedObservation N h).1
  observe := returnedObservation N
  observe_measurable := measurable_of_countable _
  current_return _ := rfl
  policy := policy
  step := returnedHistoryStep N V r d hV hr hd policy
  markov := inferInstance
  conditional_law := returned_history_conditional_law N V r d hV hr hd policy

theorem returned_history_success_lower (N : Counts) (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hscale : 200000000000 ≤ V) (hN : Restart V N) (n : ℕ) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      successfulHistoryKernel (returnedHistoryStep N V r d hV (by linarith) hd policy)
        (physicalHistorySuccess (returnedPhysicalHistory N V r d hV (by linarith) hd policy))
        (physical_history_success_measurable _) n [] Set.univ :=
  physical_history_success_lower (returnedPhysicalHistory N V r d hV (by linarith) hd policy)
    hscale hr hr' hd' n [] hN

end
end FiniteCopyReactor
