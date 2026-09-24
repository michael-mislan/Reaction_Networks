import proofs.PersisterMemory.ControlSource

namespace PersisterMemory
open Source
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def erasureAction (q : Fin 6 → ℚ) : Fin 6 → ℚ :=
  ![0, q 0-q 1, 2*(q 1-q 2), q 0-q 3, q 1+q 3-2*q 4, 2*(q 3-q 5)]

theorem controlled_residual (v : ℚ) (q : Fin 6 → ℚ) (i : Fin 6) :
    pgfResidual (1/100+v) q i = pgfResidual (1/100) q i + v*erasureAction q i := by
  fin_cases i <;> simp [pgfResidual, molecular, erasureAction] <;> ring

theorem budget_rate_bound (i : Fin 6) :
    erasureAction jointUpper i ≤ (67/73)*(1-jointUpper i) := by
  fin_cases i <;> norm_num [erasureAction, jointUpper]

theorem controlled_budget_certificate (v : ℚ) (hv : 0 ≤ v) (i : Fin 6) :
    pgfResidual (1/100+v) jointUpper i ≤ v*(67/73)*(1-jointUpper i) := by
  rw [controlled_residual]
  have hbase := uniform_joint_supersolution (1/100) (by norm_num) (by norm_num) i
  have hstep := mul_le_mul_of_nonneg_left (budget_rate_bound i) hv
  nlinarith

/-- A reusable induction step for the probability of exactly one failure. -/
theorem single_failure_step (p s q : ℝ) (hp : p ≤ 1) (hq : 0 ≤ q)
    (hq' : q ≤ 1) (hs : s ≤ 1-p) : q*s+(1-q)*p ≤ 1-q*p := by
  have h := mul_le_mul_of_nonneg_left hs hq
  have hprod := mul_nonneg (sub_nonneg.mpr hp) (sub_nonneg.mpr hq')
  nlinarith

theorem barrier_preparation : 1-jointUpper 5 = 153/200 := by
  norm_num [jointUpper]

end PersisterMemory
