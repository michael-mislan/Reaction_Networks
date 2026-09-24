import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

noncomputable section

namespace TherapeuticWindows

abbrev Vec := Fin 6 → ℝ

def deaths : Vec := ![3/10, 3/10, 3/10, 1/100, 3/10, 1/100]
def weight (i : Fin 6) : ℝ :=
  match i.val with
  | 0 => 14
  | 1 => 11
  | 2 => 10
  | 3 => 84
  | 4 => 43
  | _ => 107

def chemistry (e : ℝ) (x : Vec) : Vec := ![
  (x 1 - x 0)/50 + (x 3 - x 0)/50,
  51/100*(x 2-x 1) + 1/100*(x 4-x 1) + e*(x 0-x 1),
  2*e*(x 1-x 2),
  51/100*(x 5-x 3) + 1/100*(x 4-x 3) + e*(x 0-x 3),
  (e+1/4)*(x 1+x 3-2*x 4),
  2*e*(x 3-x 5)]

def daughters (x : Vec) : Vec := ![
  x 0*x 0, x 0*x 1, (x 0*x 2+x 1*x 1)/2,
  x 0*x 3, (x 0*x 4+x 1*x 3)/2, (x 0*x 5+x 3*x 3)/2]

def expectedDaughters (x : Vec) : Vec := ![
  2*x 0, x 0+x 1, (x 0+x 2)/2+x 1,
  x 0+x 3, (x 0+x 4+x 1+x 3)/2, (x 0+x 5)/2+x 3]

def meanAction (e : ℝ) (x : Vec) (i : Fin 6) : ℝ :=
  chemistry e x i + (expectedDaughters x i-x i)/10 - deaths i*x i

def branchingField (e : ℝ) (x : Vec) (i : Fin 6) : ℝ :=
  chemistry e x i + deaths i*(1-x i) + (daughters x i-x i)/10

/-- Literal polynomial expansion: the coefficient of t is A x, not -A x. -/
theorem source_linearization (e t : ℝ) (x : Vec) (i : Fin 6) :
    branchingField e (fun j => 1+t*x j) i =
    t*meanAction e x i + t^2/10*daughters x i := by
  fin_cases i <;>
    simp [branchingField, meanAction, chemistry, daughters, expectedDaughters, deaths] <;> ring

theorem source_mass (i : Fin 6) :
    daughters (fun _ => 1) i = 1 ∧ expectedDaughters (fun _ => 1) i = 2 := by
  fin_cases i <;> norm_num [daughters, expectedDaughters]

theorem weight_bounds (i : Fin 6) : 10 ≤ weight i ∧ weight i ≤ 107 := by
  fin_cases i <;> norm_num [weight]

theorem source_contraction (e : ℝ) (lo : 29/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : meanAction e weight i ≤ -(9/100)*weight i := by
  fin_cases i <;> norm_num [meanAction, chemistry, expectedDaughters, deaths, weight] <;>
    linarith

theorem source_ramp_growth (e : ℝ) (lo : 1/100 ≤ e) (hi : e ≤ 31/100)
    (i : Fin 6) : meanAction e weight i ≤ (14/100)*weight i := by
  fin_cases i <;> norm_num [meanAction, chemistry, expectedDaughters, deaths, weight] <;>
    linarith

/-- The hazard domination is uniform over types and all nonnegative erasure inputs. -/
theorem source_hazard_domination (v k : ℝ) (hv : 0 ≤ v) (i : Fin 6) :
    deaths i+k ≤ 3/10+v+k := by
  fin_cases i <;> norm_num [deaths] <;> linarith

end TherapeuticWindows
