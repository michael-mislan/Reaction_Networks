import proofs.MultiConsumerPermanence.ReservoirRateRecovery
import proofs.MultiConsumerPermanence.ReservoirRateGlobalExistence
import proofs.MultiConsumerPermanence.ReservoirRateLiteralSource

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

/-- B2: one full independent-rate neighborhood and physical floor for all
reference supply values in a compact positive interval. -/
theorem robust_reservoir_multi_species_permanence (n : ℕ) (hn : 2 ≤ n)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hinterval : dmin ≤ dmax) :
    (∀ r : ReservoirRates n, ∀ y : ReservoirVector n,
      reservoirPerturbedLiteralField r y = reservoirPerturbedField r y) ∧
    ∃ delta eta : ℝ, 0 < delta ∧ 0 < eta ∧
      ∀ e d : ℝ, 1/200000 ≤ e → e ≤ 1/50000 → dmin ≤ d → d ≤ dmax →
      ∀ r : ReservoirRates n, ReservoirNear e d delta r →
      (∀ (s₀ : State) (x₀ : Fin n → ℝ) (r₀ : ℝ), s₀.Positive → (∀ i, 0 < x₀ i) → 0 < r₀ →
        ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ, ∃ R : ℝ → ℝ,
          Y 0 = s₀ ∧ x 0 = x₀ ∧ R 0 = r₀ ∧ IsReservoirRateTrajectory r Y x R) ∧
      (∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ), IsReservoirRateTrajectory r Y x R →
        ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
          eta ≤ (Y t).H ∧ eta ≤ R t ∧ ∀ i, eta ≤ x t i) := by
  obtain ⟨eta,heta,h⟩ := reservoir_robust_trajectory_floor (n := n) (by omega) dmin dmax hdmin hinterval
  refine ⟨reservoir_perturbed_literal_field_eq,reservoirRobustRadius n dmin,eta,
    reservoirRobustRadius_pos n dmin hdmin,heta,?_⟩
  intro e d he he' hd hd' r hr
  exact ⟨reservoir_rate_positive_global_solution (by omega) e d dmin _ r hr hdmin hd
    (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _)) he he',h e d he he' hd hd' r hr⟩

end MultiConsumerPermanence
