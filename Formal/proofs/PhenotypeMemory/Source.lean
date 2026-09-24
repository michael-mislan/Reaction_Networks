import Mathlib

namespace PhenotypeMemory

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

end PhenotypeMemory
