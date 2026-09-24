import proofs.OverlappingSiphonInvasion.Membership
import proofs.OverlappingSiphonInvasion.OverlapFactorization
import proofs.OverlappingSiphonInvasion.GlobalExistence
import proofs.OverlappingSiphonInvasion.SpeciesRecovery

noncomputable section
namespace OverlappingSiphonInvasion
open Filter Topology
open CoreCriticalSiphon

/-- A literal overlapping-minimal-siphon source with positive global solutions
and one uniform eventual concentration floor for every positive trajectory.
This fixed-rate theorem is a milestone, not the full parameter classification. -/
theorem witness_permanence :
    PositiveRates (witness 1) ∧
    (∀ S : Finset (Fin 4), IsSiphon source S ↔
      S = ∅ ∨ S = siphonA ∨ S = siphonB ∨ S = {1,2,3}) ∧
    (∀ x₀ : State, (∀ i, 0 < x₀ i) →
      ∃ X : ℝ → State, X 0 = x₀ ∧ IsTrajectory (witness 1) X) ∧
    ∃ η : ℝ, 0 < η ∧ ∀ X : ℝ → State, IsTrajectory (witness 1) X →
      ∀ᶠ t in atTop, ∀ i, η ≤ X t i ∧ X t i ≤ 5 := by
  exact ⟨witness_positive 1 (by norm_num),source_siphons,witness_positive_global,
    speciesFloor,speciesFloor_pos,witness_trajectory_permanence⟩

end OverlappingSiphonInvasion
