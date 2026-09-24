import proofs.CompositionalMemory.TwoSpeciesCore

namespace CompositionalMemory

def twoConsume : Fin 5 → Fin 2 → ℕ := ![![0,0],![0,1],![2,0],![1,1],![1,0]]
def twoProduce : Fin 5 → Fin 2 → ℕ := ![![1,0],![2,0],![1,1],![0,1],![0,0]]
noncomputable def twoCoeff : Fin 5 → ℝ := ![6,1,6,1/6,11]
def twoStoich (r : Fin 5) : TwoPoint := fun a => (twoProduce r a:ℝ)-(twoConsume r a:ℝ)

theorem two_coeff_nonneg (r : Fin 5) : 0 ≤ twoCoeff r := by
  fin_cases r <;> norm_num [twoCoeff]

theorem two_mass_action_field (u : TwoPoint) :
    (∑ r : Fin 5, (twoCoeff r*(∏ a : Fin 2, (u a)^(twoConsume r a))) • twoStoich r)=twoField u := by
  funext a
  fin_cases a <;>
    norm_num [Fin.sum_univ_succ,Fin.prod_univ_succ,twoCoeff,twoConsume,twoProduce,twoStoich,twoField] <;> ring

theorem two_stoich_norm (r : Fin 5) : ‖twoStoich r‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num)).mpr
  intro a
  fin_cases r <;> fin_cases a <;> norm_num [twoStoich,twoProduce,twoConsume]

theorem two_activity_bound : (∑ r : Fin 5, twoCoeff r*55^(∑ a : Fin 2, twoConsume r a)) ≤ 20000 := by
  norm_num [Fin.sum_univ_succ,twoCoeff,twoConsume]

theorem two_propensity_bias_bound :
    (∑ r : Fin 5, (twoCoeff r*(∑ a : Fin 2, twoConsume r a:ℕ)^2*56^(∑ a : Fin 2, twoConsume r a))*
      ‖twoStoich r‖) ≤ 160000 := by
  calc
    _ ≤ ∑ r : Fin 5, (twoCoeff r*(∑ a : Fin 2, twoConsume r a:ℕ)^2*56^(∑ a : Fin 2, twoConsume r a))*2 := by
      apply Finset.sum_le_sum
      intro r _
      have hc := two_coeff_nonneg r
      exact mul_le_mul_of_nonneg_left (two_stoich_norm r) (by positivity)
    _ ≤ 160000 := by norm_num [Fin.sum_univ_succ,twoCoeff,twoConsume]

end CompositionalMemory
