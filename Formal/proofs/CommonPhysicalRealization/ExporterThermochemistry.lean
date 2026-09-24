import proofs.CommonPhysicalRealization.ExporterSource
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CommonPhysicalRealization
noncomputable section
open scoped BigOperators

def standardPotential : Fin 8 → ℝ :=
  ![0,0,-Real.log 10,-Real.log 10,-Real.log 10,-2*Real.log 10,
    Real.log 10 + Real.log 8000000000,0]
def forwardCoefficient (r d : ℝ) : Fin 6 → ℝ := ![1/500000000,20,20,20,r,d]
def reverseCoefficient (r d : ℝ) : Fin 6 → ℝ := ![1/5000000000,20,20,2,r,d/8000000000]

/-- Internal count mass-action factors of the displayed full complexes after
buffering F and P; products of distinct reactants and the exact X factorial. -/
def forwardSubstrate (N : RandomViability.Binding.Counts) (V aF : ℝ) : Fin 6 → ℝ :=
  ![(N 0:ℝ)*(N 1)/V,(N 2:ℝ)*(N 0)/V,(N 3:ℝ)*(N 1)/V,N 4,N 5,aF*(N 2)]
def reverseSubstrate (N : RandomViability.Binding.Counts) (V aP : ℝ) : Fin 6 → ℝ :=
  ![N 2,N 3,N 4,N 5,(N 2*(N 2-1):ℕ)/V,aP*(N 0)*(N 1)/V]

theorem coefficient_binding (N : RandomViability.Binding.Counts) (V r d aF aP : ℝ)
    (j : Fin 6) :
    physicalRate N V r d aF aP (pairForward j) =
      forwardCoefficient r d j * forwardSubstrate N V aF j ∧
    physicalRate N V r d aF aP (pairReverse j) =
      reverseCoefficient r d j * reverseSubstrate N V aP j := by
  fin_cases j <;> constructor <;>
    dsimp [physicalRate,pairForward,pairReverse,forwardCoefficient,reverseCoefficient,
      forwardSubstrate,reverseSubstrate] <;> ring

theorem common_thermochemistry (r d : ℝ) (hr : 0 < r) (hd : 0 < d) (j : Fin 6) :
    0 < forwardCoefficient r d j ∧ 0 < reverseCoefficient r d j ∧
    Real.log (forwardCoefficient r d j / reverseCoefficient r d j) =
      ∑ i, ((pairLeft j i : ℝ) - pairRight j i) * standardPotential i := by
  have hr0 := ne_of_gt hr
  have hd0 := ne_of_gt hd
  fin_cases j <;>
    norm_num [forwardCoefficient,reverseCoefficient,pairLeft,pairRight,
      standardPotential,Fin.sum_univ_succ,hr,hd,hr0,hd0,div_div]
  field_simp
  ring

theorem finite_fuel_force : standardPotential 6 - standardPotential 7 =
    Real.log 80000000000 := by
  change Real.log 10 + Real.log 8000000000 - 0 = Real.log 80000000000
  rw [sub_zero]
  rw [← Real.log_mul (by norm_num : (10:ℝ)≠0) (by norm_num : (8000000000:ℝ)≠0)]
  norm_num

end
end CommonPhysicalRealization
