import proofs.DisguisedToricAssemblies.CACParameterLocus

namespace DisguisedToricAssemblies
open CoreCouplingCAC

def exponents : Fin 8 → Fin 4 → ℕ :=
  ![![0,0,0,0], ![1,0,0,0], ![0,1,1,0], ![0,0,1,0],
    ![0,0,0,1], ![0,0,2,0], ![0,1,0,0], ![2,0,0,0]]

theorem complex_exponents (i : Fin 8) (k : Fin 4) : complexes i k = (exponents i k : ℝ) := by
  fin_cases i <;> fin_cases k <;> norm_num [complexes,exponents]

theorem activity_monomial (x : State) (i : Fin 8) :
    activity x i = ∏ k, coordinates x k ^ exponents i k := by
  fin_cases i <;> norm_num [activity,coordinates,exponents,Fin.prod_univ_succ]

noncomputable def auxiliaryDerivative (l : Fin 8 → Fin 8 → ℝ) (y : State) (k : Fin 4) : ℝ :=
  ∑ i, ∑ j, l i j*((exponents j k : ℝ)-exponents i k)*
    (∏ s, coordinates y s ^ exponents i s)

/-- The realizing network has exactly the same polynomial vector field at every state. -/
theorem realizing_field_eq (p : Rates) (x : State)
    (hp : p.Positive) (hx : x.Positive) (hs : Stationary p x)
    (hK : 0 ≤ x.A-x.B*x.z) (hJ : p.e*(x.B-x.A^2) ≤ x.B) (y : State) :
    auxiliaryDerivative (realizingRates p x) y = sourceDerivative p y := by
  have hc := (cac_constructive_sufficiency p x hp hx hs hK hJ).2.2.2
  funext k
  unfold auxiliaryDerivative
  simp_rw [← activity_monomial, ← complex_exponents]
  calc
    (∑ i, ∑ j, realizingRates p x i j*(complexes j k-complexes i k)*activity y i) =
        ∑ i, activity y i*(∑ j, realizingRates p x i j*(complexes j k-complexes i k)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ i, activity y i*coefficient p i k := by simp_rw [hc]
    _ = sourceDerivative p y k := coefficient_source p y k

/-- The criterion produces an explicit ordinary mass-action network, with zero
entries omitted from its edge set, balanced at one common positive state. -/
theorem criterion_literal_witness (p : Rates) (hp : p.Positive) (hc : ParameterCriterion p) :
    ∃ x : State, x.Positive ∧
      (∀ i j, 0 ≤ realizingRates p x i j) ∧
      (∀ i, realizingRates p x i i = 0) ∧
      (∀ i, ∑ j, realizingRates p x i j*(∏ k, coordinates x k^exponents i k) =
        ∑ j, realizingRates p x j i*(∏ k, coordinates x k^exponents j k)) ∧
      (∀ y : State, auxiliaryDerivative (realizingRates p x) y = sourceDerivative p y) := by
  obtain ⟨x,hx,hr⟩ := (cacParameterLocus p hp).mpr hc
  obtain ⟨hs,hK,hJ⟩ := (cac_state_characterization p x hp hx).mp hr
  have hw := cac_constructive_sufficiency p x hp hx hs hK hJ
  refine ⟨x,hx,hw.1,?_,?_,realizing_field_eq p x hp hx hs hK hJ⟩
  · intro i
    unfold realizingRates
    rw [(cac_flux_certificate p x hp hx hs hK hJ).2.1, zero_div]
  · simpa only [← activity_monomial] using hw.2.2.1

end DisguisedToricAssemblies
