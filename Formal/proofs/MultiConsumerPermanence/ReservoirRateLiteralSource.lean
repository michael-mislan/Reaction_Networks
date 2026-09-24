import proofs.MultiConsumerPermanence.ReservoirRateFlow
import proofs.MultiConsumerPermanence.ReservoirLiteralSource
import proofs.MultiConsumerPermanence.RateLiteralSource

namespace MultiConsumerPermanence
open scoped BigOperators
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

noncomputable def reservoirRateConsumerFlux {n : ℕ} (r : ReservoirRates n)
    (y : ReservoirVector n) (i : Fin n) : Fin 3 → ℝ :=
  ![r.reactions.k i*y (.inl 4)*y (.inl 2)*y (.inr i),
    r.reactions.mu i*y (.inr i),r.reactions.rho i*(y (.inr i))^2]

/-- Literal 15+3n independently rated channels; no equality between feed and washout. -/
noncomputable def reservoirPerturbedLiteralField {n : ℕ} (r : ReservoirRates n)
    (y : ReservoirVector n) : ReservoirVector n :=
  let f := perturbedResidentMassAction r.reactions ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3)]
  fun k => Sum.elim ![f 0,f 1,f 2,f 3,0] (fun _ => 0) k +
    (∑ j : Fin 2, reservoirFeedFlux r.feed r.wash y j*reservoirFeedChange j k) +
    ∑ i : Fin n, ∑ j : Fin 3, reservoirRateConsumerFlux r y i j*reservoirConsumerChange i j k

theorem reservoir_perturbed_literal_field_eq {n : ℕ} (r : ReservoirRates n) (y : ReservoirVector n) :
    reservoirPerturbedLiteralField r y = reservoirPerturbedField r y := by
  funext k
  cases k with
  | inl k =>
    fin_cases k <;>
      simp [reservoirPerturbedLiteralField,perturbed_resident_mass_action_eq,reservoirRateConsumerFlux,
        reservoirConsumerChange,reservoirFeedFlux,reservoirFeedChange,Fin.sum_univ_succ,
        reservoirPerturbedField,rateField,reservoirRateDonorVector,copyingLoad,rateZ,baseRates,
        Finset.mul_sum] <;> ring_nf
    all_goals
      congr 1
      congr 1
      funext i
      ring
  | inr k =>
    simp [reservoirPerturbedLiteralField,reservoirRateConsumerFlux,reservoirConsumerChange,
      reservoirFeedFlux,reservoirFeedChange,reservoirPerturbedField,Fin.sum_univ_succ,
      Finset.sum_add_distrib]
    ring

end MultiConsumerPermanence
