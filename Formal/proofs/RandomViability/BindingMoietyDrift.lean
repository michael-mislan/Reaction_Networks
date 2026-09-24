import proofs.RandomViability.BindingRateSupport

namespace RandomViability.Binding
noncomputable section
open scoped BigOperators

def uCount (N : Counts) : ℝ := ∑ i,uUnits i*(N i:ℝ)
def wCount (N : Counts) : ℝ := ∑ i,wUnits i*(N i:ℝ)

theorem uCount_expansion (N : Counts) :
    uCount N = (N 0)+(N 2)+2*(N 3)+2*(N 4)+2*(N 5) := by
  simp [uCount,uUnits,Fin.sum_univ_succ,add_assoc]

theorem wCount_expansion (N : Counts) :
    wCount N = (N 1)+(N 2)+(N 3)+2*(N 4)+2*(N 5) := by
  simp [wCount,wUnits,Fin.sum_univ_succ,add_assoc]

theorem uCount_actual_drift (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(uCount (countNext N j)-uCount N)) = V-uCount N := by
  conv_rhs => rw [uCount_expansion]
  simp only [uCount,rated_linear_jump,u_units_stoich]
  norm_num [countRate,uUnitJump,Fin.sum_univ_succ]
  ring

theorem wCount_actual_drift (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(wCount (countNext N j)-wCount N)) = V-wCount N := by
  conv_rhs => rw [wCount_expansion]
  simp only [wCount,rated_linear_jump,w_units_stoich]
  norm_num [countRate,wUnitJump,Fin.sum_univ_succ]
  ring

theorem uCount_quadratic_bound (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(uUnitJump j)^2) ≤ V+2*uCount N := by
  simp [countRate,uUnitJump,uCount,uUnits,Fin.sum_univ_succ]
  nlinarith [Nat.cast_nonneg (α := ℝ) (N 0),Nat.cast_nonneg (α := ℝ) (N 2)]

theorem wCount_quadratic_bound (N : Counts) (V eps k r : ℝ) :
    (∑ j,countRate N V eps k r j*(wUnitJump j)^2) ≤ V+2*wCount N := by
  simp [countRate,wUnitJump,wCount,wUnits,Fin.sum_univ_succ]
  nlinarith [Nat.cast_nonneg (α := ℝ) (N 1),Nat.cast_nonneg (α := ℝ) (N 2),
    Nat.cast_nonneg (α := ℝ) (N 3)]

theorem uUnitJump_bound (j : Fin 18) : |uUnitJump j| ≤ (2:ℝ) := by
  fin_cases j <;> norm_num [uUnitJump]

theorem wUnitJump_bound (j : Fin 18) : |wUnitJump j| ≤ (2:ℝ) := by
  fin_cases j <;> norm_num [wUnitJump]

theorem low_count_food_corridor (N : Counts) (V : ℝ) (hV : 0 < V)
    (hu : (9/10)*V ≤ uCount N) (hw : (9/10)*V ≤ wCount N)
    (hY : weightedCount N ≤ V/1000) :
    (4/5)*V ≤ (N 0:ℝ) ∧ (4/5)*V ≤ (N 1:ℝ) := by
  have h := free_food_from_units (N 0) (N 1) (N 2) (N 3) (N 4) (N 5)
    (by positivity) (by positivity) (by positivity) (by positivity)
  rw [uCount_expansion] at hu
  rw [wCount_expansion] at hw
  change weighted (N 2) (N 3) (N 4) (N 5) ≤ V/1000 at hY
  constructor <;> linarith [h.1,h.2]

end
end RandomViability.Binding
