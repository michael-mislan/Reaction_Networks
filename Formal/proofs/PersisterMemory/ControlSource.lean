/- Literal source and certificates copied from PhenotypeMemory with narrow imports. -/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


namespace PersisterMemory.Source

@[simp] theorem six_last {α : Type*} (a b c d e f : α) :
    (![a,b,c,d,e,f] : Fin 6 → α) 5 = f := rfl

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

/-- N=2 enumeration: U U, U R, R R, A U, A R, A A. -/
def countState : Fin 6 → ℕ × ℕ := ![(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)]

def molecular (e : ℚ) (f : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![(f 1-f 0)/50+(f 3-f 0)/50,
    51/100*(f 2-f 1)+1/100*(f 4-f 1)+e*(f 0-f 1),
    2*e*(f 1-f 2),
    51/100*(f 5-f 3)+1/100*(f 4-f 3)+e*(f 0-f 3),
    (e+1/4)*(f 1+f 3-2*f 4),
    2*e*(f 3-f 5)]

def daughter (f : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![f 0, (f 0+f 1)/2, (f 0+2*f 1+f 2)/4,
    (f 0+f 3)/2, (f 0+f 1+f 3+f 4)/4, (f 0+2*f 3+f 5)/4]

def daughterPair (z : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![z 0*z 0, z 0*z 1, (z 0*z 2+z 1*z 1)/2,
    z 0*z 3, (z 0*z 4+z 1*z 3)/2, (z 0*z 5+z 3*z 3)/2]

def death : Fin 6 → ℚ := ![3/10,3/10,3/10,1/100,3/10,1/100]

def meanAction (e : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e f i + (2*daughter f i-f i)/10-death i*f i

def pgfResidual (e : ℚ) (z : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  molecular e z i+death i*(1-z i)+(daughterPair z i-z i)/10

theorem molecular_conservative (e : ℚ) (i : Fin 6) :
    molecular e (fun _ => 1) i = 0 := by
  fin_cases i <;> norm_num [molecular]

theorem daughter_normalized (i : Fin 6) : daughter (fun _ => 1) i = 1 := by
  fin_cases i <;> norm_num [daughter]

theorem daughter_pair_normalized (i : Fin 6) : daughterPair (fun _ => 1) i = 1 := by
  fin_cases i <;> norm_num [daughterPair]

theorem mean_is_joint_linearization (e t : ℚ) (f : Fin 6 → ℚ) (i : Fin 6) :
    pgfResidual e (fun j => 1-t*f j) i =
      -t*meanAction e f i+t^2*daughterPair f i/10 := by
  fin_cases i <;> simp [pgfResidual, meanAction, molecular, daughter, daughterPair, death] <;> ring

theorem same_marginal_different_pair :
    daughterPair ![0,0,0,1,0,1] 5 = 1/2 ∧
    (daughter ![0,0,0,1,0,1] 5)^2 = 9/16 := by
  norm_num [daughterPair, daughter]

end PersisterMemory.Source



namespace PersisterMemory.Source

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

end PersisterMemory.Source
