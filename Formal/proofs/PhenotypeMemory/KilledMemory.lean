import proofs.PhenotypeMemory.Source

namespace PhenotypeMemory

attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four
  Matrix.vecHead Matrix.vecTail

def activeIndicator : Fin 6 → ℚ := ![0,0,0,1,0,1]
def restorationLower : Fin 6 → ℚ := ![1/50,1/1000,0,11/20,3/20,63/100]

/-- H v ≤ b D1 1_A, uniformly over intrinsic erasure, with death retained. -/
theorem uniform_restoration_certificate (e : ℚ)
    (he : 0 ≤ e) (he' : e ≤ 3/100) (i : Fin 6) :
    (1/10+death i)*restorationLower i-molecular e restorationLower i ≤
      daughter activeIndicator i/10 := by
  fin_cases i <;>
    norm_num [death, restorationLower, molecular, daughter, activeIndicator] <;> linarith

theorem restoration_nonnegative (i : Fin 6) : 0 ≤ restorationLower i := by
  fin_cases i <;> norm_num [restorationLower]

theorem active_restoration_bound (i : Fin 6) (hi : activeIndicator i = 1) :
    11/20 ≤ restorationLower i := by
  fin_cases i <;> norm_num [activeIndicator, restorationLower] at *

/-- A reset to U destroys A census retention with probability at least 1/4. -/
theorem one_birth_loss_bound (i : Fin 6) : daughter activeIndicator i ≤ 3/4 := by
  fin_cases i <;> norm_num [daughter, activeIndicator]

/-- Kernel induction underlying both killed retention and positive-vector bounds. -/
theorem geometric_bound {x : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h0 : x 0 ≤ 1) (hstep : ∀ n, x (n+1) ≤ c*x n) :
    ∀ n, x n ≤ c^n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    calc
      x (n+1) ≤ c*x n := hstep n
      _ ≤ c*c^n := mul_le_mul_of_nonneg_left ih hc
      _ = c^(n+1) := by ring

end PhenotypeMemory
