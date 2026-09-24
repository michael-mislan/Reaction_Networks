import proofs.FiniteCopy.FiniteJump

namespace MemoryPrediction
noncomputable section
open FiniteCopy

/-- Counts zero through five are retained; six is the killing cemetery.
The rates are the worst demographic extremes for decreasing observables. -/
def scalarKilled : FiniteJumpModel (Fin 7) Bool where
  next n e := if e then
    (if h : n.val < 6 then ⟨n.val+1, by omega⟩ else n)
    else ⟨n.val-1, by omega⟩
  rate n e := if n.val = 6 then 0 else
    (if e then 501/5000 else 1/20)*(n.val : ℝ)
  nonneg n e := by split_ifs <;> positivity

theorem scalar_total_bound (n : Fin 7) : scalarKilled.total n ≤ 1 := by
  fin_cases n <;> norm_num [FiniteJumpModel.total, scalarKilled]

def scalarKernel := scalarKilled.uniformize 1 (by norm_num) scalar_total_bound

private theorem mk2 (h : 2 < 7) : (⟨2,h⟩ : Fin 7) = 2 := rfl
private theorem mk3 (h : 3 < 7) : (⟨3,h⟩ : Fin 7) = 3 := rfl
private theorem mk4 (h : 4 < 7) : (⟨4,h⟩ : Fin 7) = 4 := rfl
private theorem mk5 (h : 5 < 7) : (⟨5,h⟩ : Fin 7) = 5 := rfl
private theorem mk6 (h : 6 < 7) : (⟨6,h⟩ : Fin 7) = 6 := rfl

theorem scalar_step_antitone (g : Fin 7 → ℝ) (hg : Antitone g) :
    Antitone (scalarKernel.step g) := by
  have h01 := hg (show (0 : Fin 7) ≤ 1 by decide)
  have h12 := hg (show (1 : Fin 7) ≤ 2 by decide)
  have h23 := hg (show (2 : Fin 7) ≤ 3 by decide)
  have h34 := hg (show (3 : Fin 7) ≤ 4 by decide)
  have h45 := hg (show (4 : Fin 7) ≤ 5 by decide)
  have h56 := hg (show (5 : Fin 7) ≤ 6 by decide)
  rw [Fin.antitone_iff_succ_le]
  intro i
  simp only [scalarKernel, FiniteJumpModel.uniformize_step]
  fin_cases i <;> norm_num [FiniteJumpModel.generator, scalarKilled, mk2, mk3,
    mk4, mk5, mk6] <;> linarith

theorem scalar_step_antitone_clock (q : ℝ) (hq : 1 ≤ q)
    (hb : ∀ n, scalarKilled.total n ≤ q) (g : Fin 7 → ℝ) (hg : Antitone g) :
    Antitone ((scalarKilled.uniformize q (by linarith) hb).step g) := by
  have hq0 : 0 < q := by linarith
  have hqinv : 0 ≤ 1/q := by positivity
  have hcoef : 0 ≤ 1-1/q := by
    have : 1/q ≤ 1 := (div_le_one hq0).mpr hq
    linarith
  have he (n : Fin 7) :
      (scalarKilled.uniformize q (by linarith) hb).step g n =
        (1-1/q)*g n+(1/q)*scalarKernel.step g n := by
    simp only [scalarKernel, FiniteJumpModel.uniformize_step, div_one]
    ring
  intro i j hij
  rw [he, he]
  exact add_le_add (mul_le_mul_of_nonneg_left (hg hij) hcoef)
    (mul_le_mul_of_nonneg_left (scalar_step_antitone g hg hij) hqinv)

def decreasingKilled (g : Fin 7 → ℝ) : Prop :=
  Antitone g ∧ (∀ n, 0 ≤ g n) ∧ g 6 = 0

theorem scalar_preserves (q : ℝ) (hq : 1 ≤ q)
    (hb : ∀ n, scalarKilled.total n ≤ q) (g : Fin 7 → ℝ) (hg : decreasingKilled g) :
    decreasingKilled ((scalarKilled.uniformize q (by linarith) hb).step g) := by
  refine ⟨scalar_step_antitone_clock q hq hb g hg.1, ?_, ?_⟩
  · intro n
    have h := (scalarKilled.uniformize q (by linarith) hb).step_mono hg.2.1 n
    simpa only [FiniteKernel.step_const] using h
  · rw [FiniteJumpModel.uniformize_step]
    norm_num [FiniteJumpModel.generator, scalarKilled, hg.2.2]

def scalarPayoff (n : Fin 7) : ℝ := if n.val ≤ 4 then 1 else 0

theorem scalarPayoff_decreasing : decreasingKilled scalarPayoff := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    unfold scalarPayoff
    split_ifs <;> norm_num at *
    omega
  · intro n
    unfold scalarPayoff
    split_ifs <;> norm_num
  · norm_num [scalarPayoff]

end
end MemoryPrediction
