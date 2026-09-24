import proofs.PhenotypeMemory.Source

namespace PhenotypeMemory

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def extinctionWeight : Fin 6 → ℚ := ![14,11,10,84,43,107]
def jointUpper : Fin 6 → ℚ := ![47/50,491/500,987/1000,27/100,147/200,47/200]
def wideUpper : Fin 6 → ℚ := ![24/25,99/100,199/200,21/50,4/5,37/100]

theorem extinction_weight_positive (i : Fin 6) :
    10 ≤ extinctionWeight i ∧ extinctionWeight i ≤ 107 := by
  fin_cases i <;> norm_num [extinctionWeight]

theorem uniform_extinction_certificate (e : ℚ)
    (he : 29/100 ≤ e) (he' : e ≤ 31/100) (i : Fin 6) :
    meanAction e extinctionWeight i ≤ -(9/100)*extinctionWeight i := by
  fin_cases i <;> norm_num [meanAction, molecular, daughter, death, extinctionWeight] <;> linarith

theorem uniform_joint_supersolution (e : ℚ)
    (he : 99/10000 ≤ e) (he' : e ≤ 101/10000) (i : Fin 6) :
    pgfResidual e jointUpper i ≤ 0 := by
  fin_cases i <;> norm_num [pgfResidual, molecular, daughterPair, death, jointUpper] <;> linarith

theorem uniform_wide_supersolution (e : ℚ)
    (he : 1/100 ≤ e) (he' : e ≤ 3/100) (i : Fin 6) :
    pgfResidual e wideUpper i ≤ 0 := by
  fin_cases i <;> norm_num [pgfResidual, molecular, daughterPair, death, wideUpper] <;> linarith

theorem upper_vectors_subunit (i : Fin 6) :
    0 ≤ jointUpper i ∧ jointUpper i < 1 ∧ 0 ≤ wideUpper i ∧ wideUpper i < 1 := by
  fin_cases i <;> norm_num [jointUpper, wideUpper]

theorem preparation_bound_values : jointUpper 5 = 47/200 ∧ wideUpper 5 = 37/100 := by
  norm_num [jointUpper, wideUpper]

end PhenotypeMemory
