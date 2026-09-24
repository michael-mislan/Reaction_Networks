import proofs.MultiConsumerPermanence.Flow

namespace MultiConsumerPermanence
open scoped BigOperators
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence

/-- Thirteen resident channels, in the same order as the donor source. -/
def residentReactants : Fin 13 → Fin 4 → ℕ :=
  ![![0,0,0,0],![0,0,0,0],![1,0,0,0],![0,1,1,0],
    ![1,0,0,0],![0,1,0,0],![0,1,0,0],![2,0,0,0],
    ![0,0,1,0],![0,0,2,0],![0,0,0,1],![0,0,0,1],![0,0,0,1]]

def residentProducts : Fin 13 → Fin 4 → ℕ :=
  ![![1,0,0,0],![0,1,0,0],![0,1,1,0],![1,0,0,0],
    ![0,0,0,0],![0,0,0,0],![2,0,0,0],![0,1,0,0],
    ![0,0,0,1],![0,0,0,1],![0,0,1,0],![0,0,2,0],![0,0,0,0]]

noncomputable def residentRates (e : ℝ) : Fin 13 → ℝ :=
  ![6,27,1,1,1,1,e,e,16,2,1,1,1/10000]

noncomputable def residentMassAction (e : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun i => ∑ j : Fin 13, residentRates e j*(∏ k : Fin 4, y k^residentReactants j k)*
    ((residentProducts j i:ℝ)-(residentReactants j i:ℝ))

/-- Consumer channels are Xi+z -> 2Xi, Xi -> 0, 2Xi -> Xi.
The coefficients below are their literal mass-action fluxes. -/
noncomputable def consumerFlux {n : ℕ} (y : Vector n) (i : Fin n) : Fin 3 → ℝ :=
  ![y (.inl 2)*y (.inr i),(1/2:ℝ)*y (.inr i),(n:ℝ)*(y (.inr i))^2]

def consumerChange {n : ℕ} (i : Fin n) : Fin 3 → (Fin 4 ⊕ Fin n) → ℝ :=
  fun j k => match k with
    | .inl a => if a = 2 ∧ j = 0 then -1 else 0
    | .inr a => if a = i then ![(1:ℝ),-1,-1] j else 0

noncomputable def literalField {n : ℕ} (e : ℝ) (y : Vector n) : Vector n :=
  fun k => Sum.elim (residentMassAction e (fun i => y (.inl i))) (fun _ => 0) k +
    ∑ i : Fin n, ∑ j : Fin 3, consumerFlux y i j*consumerChange i j k

theorem resident_mass_action_eq (e : ℝ) (y : Fin 4 → ℝ) :
    residentMassAction e y = ![fA (flagshipRates e) (y 0) (y 1) (y 2),
      fB (flagshipRates e) (y 0) (y 1) (y 2),
      fZ (flagshipRates e) (y 0) (y 1) (y 2) (y 3),
      fH (flagshipRates e) (y 2) (y 3)] := by
  funext i
  fin_cases i <;>
    simp [residentMassAction,residentRates,residentReactants,residentProducts,
      Fin.sum_univ_succ,Fin.prod_univ_succ,fA,fB,fZ,fH,flagshipRates] <;> ring

theorem literal_field_eq {n : ℕ} (e : ℝ) (y : Vector n) : literalField e y = field e y := by
  funext k
  cases k with
  | inl k =>
    fin_cases k <;>
      simp [literalField,resident_mass_action_eq,consumerFlux,consumerChange,
        field,consumerField,donorVector,total,Finset.mul_sum]
    ring
  | inr k =>
    simp [literalField,consumerFlux,consumerChange,field,Fin.sum_univ_succ]
    ring

end MultiConsumerPermanence
