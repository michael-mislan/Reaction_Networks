import proofs.FiniteCopyReactor.EndpointMeasure
import proofs.FiniteCopyReactor.CausalClock

namespace FiniteCopyReactor
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability FiniteCopy
open scoped ENNReal

theorem endpoint_observable_mono {α β : Type*} (f g : α → ℝ≥0∞) (h : ∀ x,f x ≤ g x)
    (T : ℝ) (z : ℕ → JumpState α β) : endpointObservable f T z ≤ endpointObservable g T z := by
  apply ENNReal.tsum_le_tsum
  intro k
  split_ifs
  · exact h _
  · exact le_rfl

theorem chronological_endpoint_mono {α β : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]
    (next : α → β → α) (rate : α → β → ℝ) (hr : ∀ x b,0 ≤ rate x b) (ht : ∀ x,0 < ∑ b,rate x b)
    (f g : α → ℝ≥0∞) (h : ∀ x,f x ≤ g x) (x : α) (T : ℝ) :
    chronologicalEndpoint next rate hr ht f x T ≤ chronologicalEndpoint next rate hr ht g x T :=
  lintegral_mono (endpoint_observable_mono f g h T)

theorem causal_clock_mono {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (q T : ℝ) (f g : α → ℝ≥0∞) (h : ∀ x,f x ≤ g x) (x : α) :
    causalClockEndpoint P q f x T ≤ causalClockEndpoint P q g x T := by
  unfold causalClockEndpoint
  split_ifs
  · apply ENNReal.tsum_le_tsum
    intro n
    exact mul_le_mul_right (tick_value_mono P n f g h x) _
  · exact le_rfl

theorem mask_eq_of_zero {α : Type*} (D : Set α) (f : α → ℝ≥0∞) (h : ∀ x,x ∉ D → f x=0) :
    (fun x => if x ∈ D then f x else 0)=f := by
  funext x
  by_cases hx : x ∈ D
  · exact if_pos hx
  · rw [if_neg hx,h x hx]

end
end FiniteCopyReactor
