import proofs.RandomViability.BindingCountChannels

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def reactants : Fin 18 → Fin 6 → ℕ :=
  ![![1,1,0,0,0,0], ![0,0,1,0,0,0],
    ![1,0,1,0,0,0], ![0,0,0,1,0,0],
    ![0,1,0,1,0,0], ![0,0,0,0,1,0],
    ![0,0,0,0,1,0], ![0,0,0,0,0,1],
    ![0,0,0,0,0,1], ![0,0,2,0,0,0],
    ![0,0,0,0,0,0], ![0,0,0,0,0,0],
    ![1,0,0,0,0,0], ![0,1,0,0,0,0],
    ![0,0,1,0,0,0], ![0,0,0,1,0,0],
    ![0,0,0,0,1,0], ![0,0,0,0,0,1]]

def products : Fin 18 → Fin 6 → ℕ :=
  ![![0,0,1,0,0,0], ![1,1,0,0,0,0],
    ![0,0,0,1,0,0], ![1,0,1,0,0,0],
    ![0,0,0,0,1,0], ![0,1,0,1,0,0],
    ![0,0,0,0,0,1], ![0,0,0,0,1,0],
    ![0,0,2,0,0,0], ![0,0,0,0,0,1],
    ![1,0,0,0,0,0], ![0,1,0,0,0,0],
    ![0,0,0,0,0,0], ![0,0,0,0,0,0],
    ![0,0,0,0,0,0], ![0,0,0,0,0,0],
    ![0,0,0,0,0,0], ![0,0,0,0,0,0]]

def countNext (N : Counts) (j : Fin 18) : Counts :=
  fun i => N i-reactants j i+products j i

def weightedSpecies : Fin 6 → ℝ := ![0,0,1,9/8,7/5,9/5]
def massSpecies : Fin 6 → ℝ := ![2,2,4,6,8,8]
def productSpecies : Fin 6 → ℝ := ![0,0,4,4,4,8]
def uUnits : Fin 6 → ℝ := ![1,0,1,2,2,2]
def wUnits : Fin 6 → ℝ := ![0,1,1,1,2,2]
def uUnitJump : Fin 18 → ℝ := ![0,0,0,0,0,0,0,0,0,0,1,0,-1,0,-1,-2,-2,-2]
def wUnitJump : Fin 18 → ℝ := ![0,0,0,0,0,0,0,0,0,0,0,1,0,-1,-1,-1,-2,-2]
def massJump : Fin 18 → ℝ := ![0,0,0,0,0,0,0,0,0,0,2,2,-2,-2,-4,-6,-8,-8]
def basalMark : Fin 18 → ℝ := ![4,-4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def catalyticMark : Fin 18 → ℝ := ![0,0,0,0,0,0,4,-4,0,0,0,0,0,0,0,0,0,0]
def exportMark : Fin 18 → ℝ := ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,4,4,8]

theorem weighted_stoich (j : Fin 18) :
    (∑ i,weightedSpecies i*((products j i:ℝ)-(reactants j i:ℝ))) = weightedJump j := by
  fin_cases j <;> norm_num [weightedSpecies,weightedJump,products,reactants,Fin.sum_univ_succ]

theorem u_units_stoich (j : Fin 18) :
    (∑ i,uUnits i*((products j i:ℝ)-(reactants j i:ℝ))) = uUnitJump j := by
  fin_cases j <;> norm_num [uUnits,uUnitJump,products,reactants,Fin.sum_univ_succ]

theorem w_units_stoich (j : Fin 18) :
    (∑ i,wUnits i*((products j i:ℝ)-(reactants j i:ℝ))) = wUnitJump j := by
  fin_cases j <;> norm_num [wUnits,wUnitJump,products,reactants,Fin.sum_univ_succ]

theorem total_mass_from_units (i : Fin 6) : massSpecies i = 2*(uUnits i+wUnits i) := by
  fin_cases i <;> norm_num [massSpecies,uUnits,wUnits]

theorem free_food_from_units (u w x c₁ c₂ z : ℝ)
    (hx : 0 ≤ x) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hz : 0 ≤ z) :
    u+x+2*c₁+2*c₂+2*z-(16/9)*weighted x c₁ c₂ z ≤ u ∧
    w+x+c₁+2*c₂+2*z-(10/7)*weighted x c₁ c₂ z ≤ w := by
  dsimp [weighted]
  constructor <;> nlinarith

theorem export_intensity_from_weight (x c₁ c₂ z : ℝ)
    (hx : 0 ≤ x) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    (5/9)*weighted x c₁ c₂ z ≤ x+c₁+c₂+z := by
  dsimp [weighted]
  nlinarith

theorem mass_stoich (j : Fin 18) :
    (∑ i,massSpecies i*((products j i:ℝ)-(reactants j i:ℝ))) = massJump j := by
  fin_cases j <;> norm_num [massSpecies,massJump,products,reactants,Fin.sum_univ_succ]

theorem product_stoich (j : Fin 18) :
    (∑ i,productSpecies i*((products j i:ℝ)-(reactants j i:ℝ))) =
      basalMark j+catalyticMark j-exportMark j := by
  fin_cases j <;> norm_num [productSpecies,basalMark,catalyticMark,exportMark,
    products,reactants,Fin.sum_univ_succ]

theorem next_linear_difference (N : Counts) (j : Fin 18) (a : Fin 6 → ℝ)
    (hf : ∀ i,reactants j i ≤ N i) :
    (∑ i,a i*(countNext N j i:ℝ))-(∑ i,a i*(N i:ℝ)) =
      ∑ i,a i*((products j i:ℝ)-(reactants j i:ℝ)) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [countNext,Nat.cast_add,Nat.cast_sub (hf i)]
  ring

theorem weighted_count_sum (N : Counts) :
    weightedCount N = ∑ i,weightedSpecies i*(N i:ℝ) := by
  simp [weightedCount,weighted,weightedSpecies,Fin.sum_univ_succ,add_assoc]

theorem weighted_actual_jump (N : Counts) (j : Fin 18)
    (hf : ∀ i,reactants j i ≤ N i) :
    weightedCount (countNext N j)-weightedCount N = weightedJump j := by
  rw [weighted_count_sum,weighted_count_sum,next_linear_difference N j weightedSpecies hf]
  exact weighted_stoich j

end
end RandomViability.Binding
