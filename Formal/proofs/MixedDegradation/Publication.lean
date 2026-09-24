import proofs.MixedDegradation.Main
import proofs.MixedDegradation.TypeVDerivative

namespace MixedDegradation.TypeV
open scoped BigOperators

/-- Matrix of the three-row tangent action; coefficients specialize to the
logarithmically scaled derivative of the reduced Type V equations. -/
def tangentMatrix (p : ReducedParams) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (if j = i then -p.b i - p.c i - p.d i else 0) +
    (if j = i+1 then p.b i + p.c i + p.k i else 0) +
    (if j = i+2 then p.b i + p.d i + p.h i else 0)

theorem tangentMatrix_action (p : ReducedParams) (z : Fin 3 → ℝ) (i : Fin 3) :
    (tangentMatrix p).mulVec z i =
      TangentRow (p.b i) (p.c i) (p.d i) (p.h i) (p.k i)
        (z i) (z (i+1)) (z (i+2)) := by
  simp only [Matrix.mulVec, dotProduct, tangentMatrix, add_mul, Finset.sum_add_distrib]
  simp
  unfold TangentRow
  ring

/-- Formal nonsingularity of the reduced derivative coefficient class. The
source-model derivative identification is stated separately in the supplement. -/
theorem tangentMatrix_nonsingular (p : ReducedParams) : (tangentMatrix p).det ≠ 0 := by
  apply TypeIIL.det_ne_zero_of_mulVec_kernel_eq_zero
  intro z hz
  apply tangent_kernel_zero p z
  intro i
  rw [← tangentMatrix_action]
  exact congrFun hz i

end MixedDegradation.TypeV
