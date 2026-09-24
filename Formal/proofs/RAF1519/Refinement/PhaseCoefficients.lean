import Mathlib

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 30000

def phaseH : Fin 4 → Fin 4 → ℝ :=
  ![![0,20,0,38],![0,5,20,0],![0,0,7,2],![0,0,20,24]]
def phaseWeight : Fin 4 → ℝ := ![1,9/8,7/5,9/5]
def phaseCoeff (j : Fin 5) : Fin 4 → ℝ :=
  match j.val with
  | 0 => ![1,0,0,0]
  | 1 => ![0,20,0,38]
  | 2 => ![0,100,1160,912]
  | 3 => ![0,500,28360,24208]
  | _ => ![0,2500,692680,637712]

theorem phaseH_nonnegative : ∀ i j, 0 ≤ phaseH i j := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [phaseH]

theorem phaseCoeff_nonnegative : ∀ j p, 0 ≤ phaseCoeff j p := by
  intro j p
  fin_cases j <;> fin_cases p <;> norm_num [phaseCoeff]

/-- Every listed row is checked against multiplication by the literal shifted
    phase matrix; the numbers are not an unchecked generator oracle. -/
theorem phaseCoeff_recurrence (j : Fin 4) (p : Fin 4) :
    phaseCoeff j.succ p = ∑ q, phaseCoeff j.castSucc q*phaseH q p := by
  fin_cases j <;> fin_cases p <;> norm_num [phaseCoeff,phaseH,Fin.sum_univ_succ,Fin.succ,Fin.castSucc,Fin.castAdd]

theorem phaseCoeff_weight_bound (j : Fin 5) :
    (∑ p, phaseCoeff j p) ≤ (3/2)*48^(j:ℕ) := by
  fin_cases j <;> norm_num [phaseCoeff,Fin.sum_univ_succ]

theorem phaseCoeff_derivative_bound (j : Fin 4) :
    (∑ p, phaseCoeff j.succ p) ≤ 60*48^(j:ℕ) := by
  fin_cases j <;> norm_num [phaseCoeff,Fin.sum_univ_succ,Fin.succ]

theorem phase_taylor_row_lower (p : Fin 4) :
    (961355/1382976)*phaseWeight p ≤
      ∑ j : Fin 5, phaseCoeff j p*(1/28)^(j:ℕ)/Nat.factorial (j:ℕ) := by
  fin_cases p <;> norm_num [phaseWeight,phaseCoeff,Fin.sum_univ_succ]

theorem phase_exponential_rational_margin :
    (2357/1000:ℝ)^2 ≤ 8*(961355/1382976) := by norm_num

end
end RAF1519.Refinement
