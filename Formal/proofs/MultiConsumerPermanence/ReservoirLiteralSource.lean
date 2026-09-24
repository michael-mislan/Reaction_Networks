import proofs.MultiConsumerPermanence.ReservoirFlow
import proofs.MultiConsumerPermanence.LiteralSource

namespace MultiConsumerPermanence
open scoped BigOperators
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

/-- Actual copying is Xi+z+R -> 2Xi, so both z and R are consumed. -/
noncomputable def reservoirConsumerFlux {n : ℕ} (y : ReservoirVector n) (i : Fin n) : Fin 3 → ℝ :=
  ![y (.inl 4)*y (.inl 2)*y (.inr i),(1/2:ℝ)*y (.inr i),(n:ℝ)*(y (.inr i))^2]

def reservoirConsumerChange {n : ℕ} (i : Fin n) : Fin 3 → (Fin 5 ⊕ Fin n) → ℝ :=
  fun j k => match k with
    | .inl a => if (a = 2 ∨ a = 4) ∧ j = 0 then -1 else 0
    | .inr a => if a = i then ![(1:ℝ),-1,-1] j else 0

/-- Separate directed channels 0 -> R and R -> 0. -/
noncomputable def reservoirFeedFlux {n : ℕ} (feed wash : ℝ) (y : ReservoirVector n) : Fin 2 → ℝ :=
  ![feed,wash*y (.inl 4)]

def reservoirFeedChange {n : ℕ} : Fin 2 → (Fin 5 ⊕ Fin n) → ℝ :=
  fun j k => if k = .inl 4 then ![(1:ℝ),-1] j else 0

noncomputable def reservoirLiteralField {n : ℕ} (e feed wash : ℝ)
    (y : ReservoirVector n) : ReservoirVector n :=
  let f := residentMassAction e ![y (.inl 0),y (.inl 1),y (.inl 2),y (.inl 3)]
  fun k => Sum.elim ![f 0,f 1,f 2,f 3,0] (fun _ => 0) k +
    (∑ j : Fin 2, reservoirFeedFlux feed wash y j*reservoirFeedChange j k) +
    ∑ i : Fin n, ∑ j : Fin 3, reservoirConsumerFlux y i j*reservoirConsumerChange i j k

theorem reservoir_literal_field_eq {n : ℕ} (e feed wash : ℝ) (y : ReservoirVector n) :
    reservoirLiteralField e feed wash y = reservoirField e feed wash y := by
  funext k
  cases k with
  | inl k =>
    fin_cases k <;>
      simp [reservoirLiteralField,resident_mass_action_eq,reservoirConsumerFlux,
        reservoirConsumerChange,reservoirFeedFlux,reservoirFeedChange,Fin.sum_univ_succ,
        reservoirField,consumerField,reservoirDonorVector,total,Finset.mul_sum] <;> ring
  | inr k =>
    simp [reservoirLiteralField,reservoirConsumerFlux,reservoirConsumerChange,
      reservoirFeedFlux,reservoirFeedChange,reservoirField,Fin.sum_univ_succ,Finset.sum_add_distrib]
    ring

end MultiConsumerPermanence
