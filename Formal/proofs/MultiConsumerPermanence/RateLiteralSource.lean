import proofs.MultiConsumerPermanence.RateFlow

namespace MultiConsumerPermanence
open scoped BigOperators
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

noncomputable def perturbedResidentMassAction {n : ℕ} (r : Rates n)
    (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => ∑ j : Fin 13, r.resident j*(∏ k : Fin 4, y k^residentReactants j k)*
    ((residentProducts j i:ℝ)-(residentReactants j i:ℝ))

noncomputable def perturbedConsumerFlux {n : ℕ} (r : Rates n) (y : Vector n)
    (i : Fin n) : Fin 3 → ℝ :=
  ![r.k i*y (.inl 2)*y (.inr i),r.mu i*y (.inr i),r.rho i*(y (.inr i))^2]

noncomputable def perturbedLiteralField {n : ℕ} (r : Rates n) (y : Vector n) : Vector n :=
  fun k => Sum.elim (perturbedResidentMassAction r (fun i => y (.inl i))) (fun _ => 0) k +
    ∑ i : Fin n, ∑ j : Fin 3, perturbedConsumerFlux r y i j*consumerChange i j k

theorem perturbed_resident_mass_action_eq {n : ℕ} (r : Rates n) (y : Fin 4 → ℝ) :
    perturbedResidentMassAction r y = ![rateA (baseRates r) (y 0) (y 1) (y 2),
      rateB (baseRates r) (y 0) (y 1) (y 2),
      rateZ (baseRates r) (y 0) (y 1) (y 2) (y 3) 0,
      rateH (baseRates r) (y 2) (y 3)] := by
  funext i
  fin_cases i <;>
    simp [perturbedResidentMassAction,residentReactants,residentProducts,
      Fin.sum_univ_succ,Fin.prod_univ_succ,rateA,rateB,rateZ,rateH,baseRates] <;> ring

theorem perturbed_literal_field_eq {n : ℕ} (r : Rates n) (y : Vector n) :
    perturbedLiteralField r y = perturbedField r y := by
  funext k
  cases k with
  | inl k =>
    fin_cases k <;>
      simp [perturbedLiteralField,perturbed_resident_mass_action_eq,perturbedConsumerFlux,
        consumerChange,perturbedField,rateField,rateDonorVector,copyingLoad,rateZ,
        baseRates,Finset.mul_sum]
    congr 1
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  | inr k =>
    simp [perturbedLiteralField,perturbedConsumerFlux,consumerChange,perturbedField,
      Fin.sum_univ_succ]
    ring

end MultiConsumerPermanence
