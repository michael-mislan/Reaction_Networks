import proofs.FiniteCopyReactor.StockInitiation
import proofs.RandomViability.BindingEntryExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding
open scoped BigOperators

theorem stock_exponential_identity (N : Counts) (V r d s : ℝ) :
    generator N V r d (fun X => Real.exp (-s*weightedCount X)) =
      Real.exp (-s*weightedCount N) *
      (∑ j,competitionRate N V (1/500000000) (1/10) r d j *
        (Real.exp (-s*weightedJump (competitionBase j))-1)) := by
  rw [generator_projection, competitionGenerator, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : competitionRate N V (1/500000000) (1/10) r d j = 0
  · simp only [hz, zero_mul, mul_zero]
  · have hj := weighted_actual_jump N (competitionBase j)
      (competition_rate_support N V (1/500000000) (1/10) r d j hz)
    have he : weightedCount (competitionNext N j) = weightedCount N+weightedJump (competitionBase j) := by
      change weightedCount (countNext N (competitionBase j)) = _
      linarith
    rw [he,show -s*(weightedCount N+weightedJump (competitionBase j)) =
      -s*weightedCount N+(-s*weightedJump (competitionBase j)) by ring,Real.exp_add]
    ring

/-- Quantitative exponential drift on the enlarged C2 guard. Stopping is still required. -/
theorem stock_exponential_drift (N : Counts) (V r d s : ℝ) (hV : 0 < V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A (concentration N V)) (hB : 9/10 ≤ B (concentration N V))
    (hY : Y (concentration N V) ≤ 3/50)
    (hu : (N 0:ℝ)/V ≤ 11/10) (hw : (N 1:ℝ)/V ≤ 11/10)
    (hx : (N 2:ℝ)/V ≤ 11/10) (hs : 0 ≤ s) (hs' : s ≤ 1/100) :
    generator N V r d (fun X => Real.exp (-s*weightedCount X)) ≤
      Real.exp (-s*weightedCount N)*(-(5/8)*s*weightedCount N) := by
  have hg := count_growth_with_initiation N V r d hV hr hr' hd hd' hA hB hY
  rw [generator_projection] at hg
  have hg' : (2/3)*weightedCount N+V/1000000000 ≤
      ∑ j,competitionRate N V (1/500000000) (1/10) r d j*weightedJump (competitionBase j) := by
    simpa only [competitionGenerator, weighted_count_sum, competition_rated_linear_jump,
      weighted_stoich] using hg
  have hq := stock_variance N V r d hV (by linarith) hr' hd' hu hw hx
  have hsum : (∑ j,competitionRate N V (1/500000000) (1/10) r d j *
      (Real.exp (-s*weightedJump (competitionBase j))-1)) ≤
      -s*(∑ j,competitionRate N V (1/500000000) (1/10) r d j*weightedJump (competitionBase j)) +
      (3/5)*s^2*competitionVariance N V (1/500000000) (1/10) r d := by
    calc
      _ ≤ ∑ j,competitionRate N V (1/500000000) (1/10) r d j *
          (-s*weightedJump (competitionBase j)+(3/5)*s^2*(weightedJump (competitionBase j))^2) := by
        apply Finset.sum_le_sum
        intro j _
        have ha : |-s*weightedJump (competitionBase j)| ≤ 9/50 := by
          rw [abs_mul,abs_neg,abs_of_nonneg hs]
          exact (mul_le_mul hs' (weightedJump_bound _) (abs_nonneg _) (by norm_num)).trans (by norm_num)
        apply mul_le_mul_of_nonneg_left _
          (competitionRate_nonneg N V (1/500000000) (1/10) r d hV
            (by norm_num) (by norm_num) (by linarith) hd j)
        nlinarith [exp_small_quadratic (-s*weightedJump (competitionBase j)) ha]
      _ = _ := by
        unfold competitionVariance
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hgs := mul_le_mul_of_nonneg_left hg' hs
  have hqs := mul_le_mul_of_nonneg_left hq (show 0 ≤ (3/5)*s^2 by positivity)
  have hsy : s^2*weightedCount N ≤ (1/100)*s*weightedCount N := by
    have hsq : s^2 ≤ (1/100)*s := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq (weightedCount_nonneg N)
  have hsv : s^2*V ≤ (1/100)*s*V := by
    have hsq : s^2 ≤ (1/100)*s := by nlinarith
    exact mul_le_mul_of_nonneg_right hsq hV.le
  rw [stock_exponential_identity]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  nlinarith [mul_nonneg hs (weightedCount_nonneg N), mul_nonneg (sq_nonneg s) hV.le]

end
end FiniteCopyReactor
