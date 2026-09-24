import proofs.MemoryPrediction.ScalarKilled
import proofs.CompositionalMemory.CanonicalFiniteLaw
import Mathlib.Analysis.Complex.ExponentialBounds

namespace MemoryPrediction
noncomputable section
open FiniteCopy CompositionalMemory

def scalarRow : ℕ → Fin 7 → ℝ
  | 0 => ![(1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (0 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 1 => ![(1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (599200 : ℝ)/1000000, (250000 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 2 => ![(1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (879519 : ℝ)/1000000, (539400 : ℝ)/1000000, (212050 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 3 => ![(1000000 : ℝ)/1000000, (1000000 : ℝ)/1000000, (975855 : ℝ)/1000000, (795351 : ℝ)/1000000, (476221 : ℝ)/1000000, (187650 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 4 => ![(1000000 : ℝ)/1000000, (997580 : ℝ)/1000000, (942096 : ℝ)/1000000, (726496 : ℝ)/1000000, (424387 : ℝ)/1000000, (165780 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 5 => ![(1000000 : ℝ)/1000000, (992141 : ℝ)/1000000, (904438 : ℝ)/1000000, (668022 : ℝ)/1000000, (381159 : ℝ)/1000000, (147375 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 6 => ![(1000000 : ℝ)/1000000, (983746 : ℝ)/1000000, (865830 : ℝ)/1000000, (617253 : ℝ)/1000000, (344830 : ℝ)/1000000, (131986 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 7 => ![(1000000 : ℝ)/1000000, (972743 : ℝ)/1000000, (827806 : ℝ)/1000000, (572649 : ℝ)/1000000, (314006 : ℝ)/1000000, (119072 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 8 => ![(1000000 : ℝ)/1000000, (959583 : ℝ)/1000000, (791166 : ℝ)/1000000, (533174 : ℝ)/1000000, (287605 : ℝ)/1000000, (108150 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 9 => ![(1000000 : ℝ)/1000000, (944728 : ℝ)/1000000, (756306 : ℝ)/1000000, (498054 : ℝ)/1000000, (264793 : ℝ)/1000000, (98830 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 10 => ![(1000000 : ℝ)/1000000, (928611 : ℝ)/1000000, (723394 : ℝ)/1000000, (466673 : ℝ)/1000000, (244927 : ℝ)/1000000, (90806 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 11 => ![(1000000 : ℝ)/1000000, (911617 : ℝ)/1000000, (692468 : ℝ)/1000000, (438524 : ℝ)/1000000, (227504 : ℝ)/1000000, (83842 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 12 => ![(1000000 : ℝ)/1000000, (894077 : ℝ)/1000000, (663492 : ℝ)/1000000, (413182 : ℝ)/1000000, (212128 : ℝ)/1000000, (77752 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 13 => ![(1000000 : ℝ)/1000000, (876268 : ℝ)/1000000, (636388 : ℝ)/1000000, (390291 : ℝ)/1000000, (198480 : ℝ)/1000000, (72392 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 14 => ![(1000000 : ℝ)/1000000, (858418 : ℝ)/1000000, (611058 : ℝ)/1000000, (369547 : ℝ)/1000000, (186306 : ℝ)/1000000, (67645 : ℝ)/1000000, (0 : ℝ)/1000000]
  | 15 => ![(1000000 : ℝ)/1000000, (840711 : ℝ)/1000000, (587395 : ℝ)/1000000, (350691 : ℝ)/1000000, (175394 : ℝ)/1000000, (63420 : ℝ)/1000000, (0 : ℝ)/1000000]
  | _ => fun _ => 0

theorem row_initial : scalarRow 0 = scalarPayoff := by
  funext i
  fin_cases i <;> norm_num [scalarRow, scalarPayoff]

set_option maxHeartbeats 800000 in
theorem row_step (n : ℕ) (hn : n < 15) (i : Fin 7) :
    scalarRow (n+1) i ≤ scalarKernel.step (scalarRow n) i := by
  rw [scalarKernel, FiniteJumpModel.uniformize_step]
  interval_cases n <;> fin_cases i <;>
    norm_num [FiniteJumpModel.generator, scalarKilled, scalarRow]

theorem row_lower (n : ℕ) (hn : n < 16) (i : Fin 7) :
    scalarRow n i ≤ scalarKernel.steps n scalarPayoff i := by
  induction n generalizing i with
  | zero => rw [row_initial]; exact le_rfl
  | succ n ih =>
    exact (row_step n (by omega) i).trans
      (scalarKernel.step_mono (ih (by omega)) i)

theorem exp_neg_seven_lower : (1/1097 : ℝ) ≤ Real.exp (-7) := by
  have he : Real.exp 1 ≤ (271829/100000 : ℝ) := by
    linarith [Real.exp_one_lt_d9]
  have hpow : (Real.exp 1)^7 ≤ (271829/100000 : ℝ)^7 := by gcongr
  have hexp : Real.exp (7 : ℝ) ≤ 1097 := by
    have hi : Real.exp (7 : ℝ) = (Real.exp 1)^7 := by
      simp [← Real.exp_nat_mul]
    rw [hi]
    exact hpow.trans (by norm_num)
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.exp_pos 7) hexp

theorem row_nonneg (n : ℕ) (hn : n < 16) (i : Fin 7) : 0 ≤ scalarRow n i := by
  interval_cases n <;> fin_cases i <;> norm_num [scalarRow]

theorem finite_scalar_certificate :
    (963/1000 : ℝ) ≤ finiteTimeExpectation scalarKilled 7 scalarPayoff 1 := by
  rw [finite_time_eq_uniformized scalarKilled 1 7 (by norm_num) scalar_total_bound]
  simp only [one_mul, NNReal.coe_one]
  change (963/1000 : ℝ) ≤ scalarKernel.poissonized 7 scalarPayoff 1
  have hf : ∀ i, 0 ≤ scalarPayoff i := scalarPayoff_decreasing.2.1
  have hs := scalarKernel.nonneg_summable 7 scalarPayoff hf 1
  have hp : (∑ n ∈ Finset.range 16, poissonWeight 7 n * scalarKernel.steps n scalarPayoff 1) ≤
      scalarKernel.poissonized 7 scalarPayoff 1 := by
    exact hs.sum_le_tsum (Finset.range 16) (fun n _ =>
      mul_nonneg (poissonWeight_nonneg 7 n) (scalarKernel.steps_nonneg n hf 1))
  have hrow : (∑ n ∈ Finset.range 16, (1/1097 : ℝ)*7^n/(n.factorial : ℝ)*scalarRow n 1) ≤
      ∑ n ∈ Finset.range 16, poissonWeight 7 n * scalarKernel.steps n scalarPayoff 1 := by
    apply Finset.sum_le_sum
    intro n hn
    have hn' : n < 16 := Finset.mem_range.mp hn
    have hc : (1/1097 : ℝ)*7^n/(n.factorial : ℝ) ≤ poissonWeight 7 n := by
      unfold poissonWeight
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right exp_neg_seven_lower (by positivity)) (by positivity)
    exact mul_le_mul hc (row_lower n hn' 1) (row_nonneg n hn' 1) (poissonWeight_nonneg 7 n)
  apply le_trans _ (hrow.trans hp)
  norm_num [Finset.sum_range_succ, scalarRow, Nat.factorial]

end
end MemoryPrediction
