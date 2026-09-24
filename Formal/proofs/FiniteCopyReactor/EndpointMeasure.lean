import proofs.FiniteCopyReactor.EndpointBounds

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability Filter
open scoped ENNReal Topology

def endpointChoice {α β : Type*} (T : ℝ) (z : ℕ → JumpState α β) (k : ℕ) : Prop :=
  (jumpElapsed z k ≤ T ∧ T < jumpElapsed z (k+1)) ∨
    (k=0 ∧ ¬∃ j,jumpElapsed z j ≤ T ∧ T < jumpElapsed z (j+1))

theorem endpoint_choice_exists {α β : Type*} (T : ℝ) (z : ℕ → JumpState α β) :
    ∃ k,endpointChoice T z k := by
  by_cases h : ∃ j,jumpElapsed z j ≤ T ∧ T < jumpElapsed z (j+1)
  · obtain ⟨j,hj⟩ := h
    exact ⟨j,Or.inl hj⟩
  · exact ⟨0,Or.inr ⟨rfl,h⟩⟩

def selectedEndpoint {α β : Type*} (T : ℝ) (z : ℕ → JumpState α β) : α :=
  (z (Nat.find (endpoint_choice_exists T z))).1

theorem endpoint_observable_selected {α β : Type*} (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) (hw : ∀ k,0 ≤ (z (k+1)).2.2)
    (hex : ∃ j,jumpElapsed z j ≤ T ∧ T < jumpElapsed z (j+1)) :
    endpointObservable f T z=f (selectedEndpoint T z) := by
  have hk : jumpElapsed z (Nat.find (endpoint_choice_exists T z)) ≤ T ∧
      T < jumpElapsed z (Nat.find (endpoint_choice_exists T z)+1) := by
    rcases Nat.find_spec (endpoint_choice_exists T z) with h | h
    · exact h
    · exact False.elim (h.2 hex)
  exact endpoint_observable_at f T z hw _ hk

section Measurability
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem selected_endpoint_joint_measurable :
    Measurable (fun p : ℝ × (ℕ → JumpState α β) => selectedEndpoint p.1 p.2) := by
  have hm (k : ℕ) : MeasurableSet {p : ℝ × (ℕ → JumpState α β) |
      jumpElapsed p.2 k ≤ p.1 ∧ p.1 < jumpElapsed p.2 (k+1)} :=
    (measurableSet_le ((jumpElapsed_measurable k).comp measurable_snd) measurable_fst).inter
      (measurableSet_lt measurable_fst ((jumpElapsed_measurable (k+1)).comp measurable_snd))
  have hAny : MeasurableSet {p : ℝ × (ℕ → JumpState α β) |
      ∃ k,jumpElapsed p.2 k ≤ p.1 ∧ p.1 < jumpElapsed p.2 (k+1)} := by
    simp only [Set.setOf_exists]
    exact MeasurableSet.iUnion hm
  have hp (k : ℕ) : MeasurableSet {p : ℝ × (ℕ → JumpState α β) | endpointChoice p.1 p.2 k} := by
    by_cases hk : k=0
    · simpa only [endpointChoice,hk,true_and,Set.setOf_or] using (hm 0).union hAny.compl
    · simpa only [endpointChoice,hk,false_and,or_false] using hm k
  exact Measurable.find (fun k => ((measurable_pi_apply k).comp measurable_snd).fst) hp
    (fun p => endpoint_choice_exists p.1 p.2)

theorem selected_endpoint_measurable (T : ℝ) : Measurable (selectedEndpoint (α := α) (β := β) T) :=
  selected_endpoint_joint_measurable.comp (measurable_const.prodMk measurable_id)
end Measurability

variable {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

def chronologicalMeasure (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (x : α) (T : ℝ) : Measure α :=
  (jumpTrajectoryLaw x next rate hr ht).map (selectedEndpoint T)

instance chronologicalMeasure_probability (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (x : α) (T : ℝ) :
    IsProbabilityMeasure (chronologicalMeasure next rate hr ht x T) :=
  Measure.isProbabilityMeasure_map (selected_endpoint_measurable T).aemeasurable

theorem chronological_endpoint_measure (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (x : α) (T : ℝ) (hT : 0 ≤ T)
    (hn : ∀ᵐ z ∂jumpTrajectoryLaw x next rate hr ht,Tendsto (jumpElapsed z) atTop atTop)
    (f : α → ℝ≥0∞) :
    chronologicalEndpoint next rate hr ht f x T=∫⁻ y,f y ∂chronologicalMeasure next rate hr ht x T := by
  unfold chronologicalMeasure
  rw [lintegral_map (measurable_of_countable f) (selected_endpoint_measurable T)]
  have hw := jumpTrajectory_wait_nonneg x next rate hr ht
  apply lintegral_congr_ae
  filter_upwards [hw,hn] with z hwait hdiv
  exact endpoint_observable_selected f T z hwait (endpoint_interval_exists z T hT hdiv)

def chronologicalKernel (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (T : ℝ) : Kernel α α :=
  Kernel.ofFunOfCountable (fun x => chronologicalMeasure next rate hr ht x T)

instance chronologicalKernel_markov (next : α → β → α) (rate : α → β → ℝ)
    (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b) (T : ℝ) :
    IsMarkovKernel (chronologicalKernel next rate hr ht T) where
  isProbabilityMeasure x := chronologicalMeasure_probability next rate hr ht x T

end
end FiniteCopyReactor
