import proofs.MultiConsumerPermanence.RateRecovery
import proofs.MultiConsumerPermanence.RateGlobalExistence
import proofs.MultiConsumerPermanence.RateLiteralSource

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

/-- A2: all 13+3n directed rates vary independently in a nonzero cube.
The physical floor is uniform over the cube, e, and all positive initial states. -/
theorem robust_multi_species_permanence (n : ℕ) (hn : 2 ≤ n) :
    (∀ r : Rates n, ∀ y : Vector n, perturbedLiteralField r y = perturbedField r y) ∧
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧
      ∀ e : ℝ, 1/200000 ≤ e → e ≤ 1/50000 →
      ∀ r : Rates n, Near e delta r →
      (∀ (s₀ : State) (x₀ : Fin n → ℝ), s₀.Positive → (∀ i, 0 < x₀ i) →
        ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ,
          Y 0 = s₀ ∧ x 0 = x₀ ∧ IsPerturbedTrajectory r Y x) ∧
      (∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ), IsPerturbedTrajectory r Y x →
        ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
          eta ≤ (Y t).H ∧ ∀ i, eta ≤ x t i) := by
  obtain ⟨eta,heta,h⟩ := robust_trajectory_floor (n := n) (by omega)
  refine ⟨perturbed_literal_field_eq,robustRadius n,eta,robustRadius_pos n,heta,?_⟩
  intro e he he' r hr
  exact ⟨perturbed_positive_global_solution (by omega) e _ r hr (min_le_left _ _) he he',
    h e he he' r hr⟩

end MultiConsumerPermanence
