import proofs.CoreInteraction.Degradation.Star

namespace CoreInteraction.Examples.DegradationStar

open CoreInteraction.Degradation DegradationControl

def oneBranch : StarData Unit Unit where
  rootDiagonal := -1
  internal := fun _ _ _ => -15
  toRoot := fun _ _ => 3
  fromRoot := fun _ _ => 3

def twoBranch : StarData (Fin 2) Unit where
  rootDiagonal := -1
  internal := fun _ _ _ => -15
  toRoot := fun _ _ => 3
  fromRoot := fun _ _ => 3

noncomputable def oneSolve : Unit → Unit → ℝ := fun _ _ => 1 / 5
noncomputable def twoSolve : Fin 2 → Unit → ℝ := fun _ _ => 1 / 5

theorem oneSolve_exact : oneBranch.SolveWitness oneSolve := by
  intro i j
  cases i
  cases j
  norm_num [StarData.SolveWitness, oneBranch, oneSolve, Matrix.mulVec, dotProduct]

theorem twoSolve_exact : twoBranch.SolveWitness twoSolve := by
  intro i j
  fin_cases i <;> cases j <;>
    norm_num [StarData.SolveWitness, twoBranch, twoSolve, Matrix.mulVec, dotProduct]

theorem oneSolve_positive : oneBranch.PositiveInternal oneSolve := by
  intro i j
  cases i
  cases j
  norm_num [StarData.PositiveInternal, oneSolve]

theorem twoSolve_positive : twoBranch.PositiveInternal twoSolve := by
  intro i j
  fin_cases i <;> cases j <;> norm_num [StarData.PositiveInternal, twoSolve]

theorem oneCoupling_positive : oneBranch.PositiveRootCoupling := by
  intro i j
  cases i
  cases j
  norm_num [StarData.PositiveRootCoupling, oneBranch]

theorem twoCoupling_positive : twoBranch.PositiveRootCoupling := by
  intro i j
  fin_cases i <;> cases j <;>
    norm_num [StarData.PositiveRootCoupling, twoBranch]

theorem oneBranch_schurLoad : oneBranch.schurLoad oneSolve = -(2 / 5 : ℝ) := by
  norm_num [StarData.schurLoad, StarData.load, oneBranch, oneSolve]

theorem twoBranch_schurLoad : twoBranch.schurLoad twoSolve = (1 / 5 : ℝ) := by
  norm_num [StarData.schurLoad, StarData.load, twoBranch, twoSolve, Fin.sum_univ_two]

theorem oneBranch_extinction : ExtinctionCertificate oneBranch.matrix := by
  apply (oneBranch.schurLoad_trichotomy oneSolve oneSolve_exact oneSolve_positive
    oneCoupling_positive).2.2
  rw [oneBranch_schurLoad]
  norm_num

theorem twoBranch_growth : GrowthCertificate twoBranch.matrix := by
  apply (twoBranch.schurLoad_trichotomy twoSolve twoSolve_exact twoSolve_positive
    twoCoupling_positive).1
  rw [twoBranch_schurLoad]
  norm_num

/-- Exact local-extinction/global-growth diagnostic from the implementation
guide: duplicating an extinct branch at one shared root changes the Schur load
from `-2/5` to `1/5` and produces a strict growth certificate. -/
theorem localExtinction_globalGrowth :
    ExtinctionCertificate oneBranch.matrix ∧ GrowthCertificate twoBranch.matrix :=
  ⟨oneBranch_extinction, twoBranch_growth⟩

end CoreInteraction.Examples.DegradationStar
