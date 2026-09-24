import proofs.MultiConsumerPermanence.ReferencePermanence
import proofs.MultiConsumerPermanence.GlobalExistence
import proofs.MultiConsumerPermanence.LiteralSource

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

/-- Root A1: literal interacting multi-consumer source, global positive
existence for every positive initial state, and a common physical species floor.
The floor depends on n but not on e or the initial condition. -/
theorem reference_multi_species_permanence (n : ℕ) (hn : 2 ≤ n) :
    (∀ e : ℝ, ∀ y : Vector n, literalField e y = field e y) ∧
    ∃ eta : ℝ, 0 < eta ∧ ∀ e : ℝ, 1/200000 ≤ e → e ≤ 1/50000 →
      (∀ (s₀ : State) (x₀ : Fin n → ℝ), s₀.Positive → (∀ i, 0 < x₀ i) →
        ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ,
          Y 0 = s₀ ∧ x 0 = x₀ ∧ IsMultiTrajectory n e Y x) ∧
      (∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ), IsMultiTrajectory n e Y x →
        ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
          eta ≤ (Y t).H ∧ ∀ i, eta ≤ x t i) := by
  obtain ⟨eta,heta,h⟩ := reference_trajectory_permanence (n := n) (by omega)
  refine ⟨literal_field_eq,eta,heta,?_⟩
  intro e he he'
  have he0 : 0 ≤ e := by linarith
  exact ⟨positive_global_solution n e he0 he',h e he0 he'⟩

end MultiConsumerPermanence
