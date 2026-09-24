import proofs.PhenotypeMemory.ReductionCertificate
import proofs.PhenotypeMemory.IndependentUpper
namespace PhenotypeMemory
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail
def responseWeight : Fin 6 → ℚ := ![537/250,2011/1000,1997/1000,122/25,1441/500,979/200]
def independentJacobian (z w : Fin 6 → ℚ) (i : Fin 6) : ℚ :=
  ∑ j : Fin 6, eventInverse i j * daughter z j * daughter w j / 5
set_option maxHeartbeats 800000 in
theorem weighted_source_contraction (i : Fin 6) :
    0 < responseWeight i ∧
    independentJacobian independentUpper responseWeight i ≤ (796/1000)*responseWeight i := by
  fin_cases i <;> norm_num [independentJacobian, responseWeight, independentUpper,
    eventInverse, daughter, Fin.sum_univ_succ]
end PhenotypeMemory
