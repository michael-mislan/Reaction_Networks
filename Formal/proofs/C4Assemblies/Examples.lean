import proofs.C4Assemblies.Resolution
import proofs.C4Assemblies.Thermochemistry
import proofs.C4Assemblies.Synthesis
import proofs.C4Assemblies.SupplyCeiling
import proofs.C4Assemblies.BudgetSafety
import proofs.C4Assemblies.PhaseFaces
import proofs.C4Assemblies.Cutoff

namespace C4Assemblies
noncomputable section
open ProductiveRecovery MeasureTheory

private theorem vector_six_last (a b c d e f : ℝ) :
    ![a,b,c,d,e,f] (5 : Fin 6) = f := rfl

def pathExchange (i j : Fin 4) : ℝ :=
  if i.val+1=j.val ∨ j.val+1=i.val then 1/2 else 0
def ringExchange (i j : Fin 4) : ℝ :=
  if i.val+1=j.val ∨ j.val+1=i.val ∨ (i.val=0 ∧ j.val=3) ∨ (i.val=3 ∧ j.val=0) then 1/2 else 0

def pathParameters : Parameters (Fin 4) where
  k := pathExchange
  r := ![19,21,19,21]
  d := ![1/25,1/50,1/50,1/25]
  exchange_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [pathExchange]
  exchange_symmetric := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [pathExchange]
  exchange_diagonal := by intro i; fin_cases i <;> norm_num [pathExchange]
  r_lower := by intro i; fin_cases i <;> norm_num
  r_upper := by intro i; fin_cases i <;> norm_num
  d_lower := by intro i; fin_cases i <;> norm_num
  d_upper := by intro i; fin_cases i <;> norm_num

def ringParameters : Parameters (Fin 4) where
  k := ringExchange
  r := pathParameters.r
  d := pathParameters.d
  exchange_nonneg := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [ringExchange]
  exchange_symmetric := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [ringExchange]
  exchange_diagonal := by intro i; fin_cases i <;> norm_num [ringExchange]
  r_lower := pathParameters.r_lower
  r_upper := pathParameters.r_upper
  d_lower := pathParameters.d_lower
  d_upper := pathParameters.d_upper

def heterogeneousReady : Assembly (Fin 4) :=
  ![![(159/160)-(1/20),(159/160)-(1/20),1/20,0,0,0],
    ![(159/160)-(4/45),(159/160)-(2/45),0,2/45,0,0],
    ![(159/160)-(1/14),(159/160)-(1/14),0,0,1/28,0],
    ![(159/160)-(1/18),(159/160)-(1/18),0,0,0,1/36]]

theorem heterogeneous_ready : AssemblyReady heterogeneousReady := by
  have hn : ∀ i, Nonneg (heterogeneousReady i) := by
    intro i s
    fin_cases i <;> fin_cases s <;> norm_num [heterogeneousReady]
  intro i
  refine ⟨hn i,?_,?_,?_⟩ <;> fin_cases i <;>
    norm_num [A,B,Y,heterogeneousReady, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ', vector_six_last]

def fixedPulse : Intervention where
  q := 1/2
  loss := fun _ => 49/50
  eU := -(1/200)
  eW := -(1/200)
  q_lower := by norm_num
  q_upper := by norm_num
  loss_lower := by intro i; norm_num
  loss_upper := by intro i; norm_num
  eU_lower := le_rfl
  eU_upper := by norm_num
  eW_lower := le_rfl
  eW_upper := by norm_num

theorem nonzero_distinct_topologies :
    pathParameters.k 0 1 = 1/2 ∧ ringParameters.k 0 1 = 1/2 ∧
    pathParameters.k 0 3 = 0 ∧ ringParameters.k 0 3 = 1/2 ∧
    diffusion pathParameters.k (fun i => heterogeneousReady i 2) 0 = -(1/40) := by
  norm_num [pathParameters,ringParameters,pathExchange,ringExchange,diffusion,
    heterogeneousReady,Fin.sum_univ_succ, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ']

/-- Closed proof terms retain the entire quantified root conclusion. -/
def path_operation := conservative_assembly_operation pathParameters (fun _ => fixedPulse)
  (fun _ _ _ _ => fixedPulse) heterogeneousReady
  (fun i => strong_admitted _ (heterogeneous_ready i))

def ring_operation := conservative_assembly_operation ringParameters (fun _ => fixedPulse)
  (fun _ _ _ _ => fixedPulse) heterogeneousReady
  (fun i => strong_admitted _ (heterogeneous_ready i))

end
end C4Assemblies
