import proofs.MultiConsumerPermanence.ReservoirRecovery
import proofs.MultiConsumerPermanence.ReservoirGlobalExistence
import proofs.MultiConsumerPermanence.ReservoirLiteralSource

namespace MultiConsumerPermanence
open CoreCouplingCAC Filter Topology

/-- B1 with constants already uniform on compact positive supply intervals.
Independent-rate robustness and supply degeneration are separate endpoints. -/
theorem reservoir_multi_species_permanence (n : ℕ) (hn : 2 ≤ n)
    (dmin dmax : ℝ) (hdmin : 0 < dmin) (hinterval : dmin ≤ dmax) :
    (∀ e feed wash : ℝ, ∀ y : ReservoirVector n,
      reservoirLiteralField e feed wash y = reservoirField e feed wash y) ∧
    ∃ eta : ℝ, 0 < eta ∧ ∀ e d : ℝ, 1/200000 ≤ e → e ≤ 1/50000 →
      dmin ≤ d → d ≤ dmax →
      (∀ (s₀ : State) (x₀ : Fin n → ℝ) (r₀ : ℝ), s₀.Positive → (∀ i, 0 < x₀ i) → 0 < r₀ →
        ∃ Y : ℝ → State, ∃ x : ℝ → Fin n → ℝ, ∃ R : ℝ → ℝ,
          Y 0 = s₀ ∧ x 0 = x₀ ∧ R 0 = r₀ ∧ IsReservoirTrajectory n e d d Y x R) ∧
      (∀ (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ), IsReservoirTrajectory n e d d Y x R →
        ∀ᶠ t in atTop, eta ≤ (Y t).A ∧ eta ≤ (Y t).B ∧ eta ≤ (Y t).z ∧
          eta ≤ (Y t).H ∧ eta ≤ R t ∧ ∀ i, eta ≤ x t i) := by
  obtain ⟨eta,heta,h⟩ := reservoir_trajectory_permanence (n := n) (by omega) dmin dmax hdmin hinterval
  refine ⟨reservoir_literal_field_eq,eta,heta,?_⟩
  intro e d he he' hd hd'
  have he0 : 0 ≤ e := by linarith
  exact ⟨reservoir_positive_global_solution n e d he0 he' (lt_of_lt_of_le hdmin hd),
    h e d he0 he' hd hd'⟩

end MultiConsumerPermanence
