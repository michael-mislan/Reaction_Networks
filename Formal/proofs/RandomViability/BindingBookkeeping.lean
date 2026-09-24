import proofs.RandomViability.BindingRateSupport

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def countProduct (N : Counts) : ℝ := ∑ i,productSpecies i*(N i:ℝ)
def countMass (N : Counts) : ℝ := ∑ i,massSpecies i*(N i:ℝ)

theorem rated_product_change (N : Counts) (V eps k r : ℝ) (j : Fin 18) :
    countRate N V eps k r j*(countProduct (countNext N j)-countProduct N) =
      countRate N V eps k r j*(basalMark j+catalyticMark j-exportMark j) := by
  exact (rated_linear_jump N V eps k r j productSpecies).trans (by rw [product_stoich])

theorem rated_mass_change (N : Counts) (V eps k r : ℝ) (j : Fin 18) :
    countRate N V eps k r j*(countMass (countNext N j)-countMass N) =
      countRate N V eps k r j*massJump j := by
  exact (rated_linear_jump N V eps k r j massSpecies).trans (by rw [mass_stoich])

/-- The actual rate-weighted covalent stock balance includes bound-form
washout, reverse ligation and the basal contribution with their proper signs. -/
theorem actual_covalent_balance (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(countProduct (countNext N j)-countProduct N)) =
      (∑ j,countRate N V eps k r j*basalMark j)+
      (∑ j,countRate N V eps k r j*catalyticMark j)-
      (∑ j,countRate N V eps k r j*exportMark j) := by
  simp only [rated_product_change]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]

theorem export_marks_nonnegative (j : Fin 18) : 0 ≤ exportMark j := by
  fin_cases j <;> norm_num [exportMark]

end
end RandomViability.Binding
