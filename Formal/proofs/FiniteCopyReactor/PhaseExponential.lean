import proofs.FiniteCopyReactor.PhaseObservable
import proofs.FiniteCopyReactor.StockExponential

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped BigOperators

theorem phase_exponential_identity (w : PhaseWeights) (N : Counts) (V r d s : ℝ) :
    competitionGenerator N V (1/500000000) (1/10) r d (fun X => Real.exp (-s*w.obs X)) =
      Real.exp (-s*w.obs N)*(∑ j,competitionRate N V (1/500000000) (1/10) r d j*
        (Real.exp (-s*phaseJump w (competitionBase j))-1)) := by
  unfold competitionGenerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : competitionRate N V (1/500000000) (1/10) r d j=0
  · simp only [hz,zero_mul,mul_zero]
  · have hj := phase_actual_jump w N (competitionBase j)
      (competition_rate_support N V (1/500000000) (1/10) r d j hz)
    have he : w.obs (competitionNext N j)=w.obs N+phaseJump w (competitionBase j) := by
      change w.obs (countNext N (competitionBase j))=_
      linarith
    dsimp only
    rw [he,show -s*(w.obs N+phaseJump w (competitionBase j)) =
      -s*w.obs N+(-s*phaseJump w (competitionBase j)) by ring,Real.exp_add]
    ring

theorem phase_exponential_generator (w : PhaseWeights) (hw : w.Nonneg) (hm : w.mass ≤ 1)
    (N : Counts) (V : ℕ) (r d s : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) (hc : resourceGood N V) :
    competitionGenerator N V (1/500000000) (1/10) r d (fun X => Real.exp (-s*w.obs X)) ≤
      Real.exp (-s*w.obs N)*(-s*phaseDriftLower w N+7200*(V:ℝ)*s^2) := by
  let R := competitionRate N V (1/500000000) (1/10) r d
  have hn (j) : 0 ≤ R j := competitionRate_nonneg N V (1/500000000) (1/10) r d hV
    (by norm_num) (by norm_num) (by linarith) hd j
  have ht : (∑ j,R j) ≤ 3000*(V:ℝ) := by
    apply competition_total_rate_bound N V (1/500000000) (1/10) r d hV
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by linarith) (by linarith) hd (by linarith)
    intro i
    linarith [resource_count_cap N V hc i]
  have hl (j) : Real.exp (-s*phaseJump w (competitionBase j))-1 ≤
      -s*phaseJump w (competitionBase j)+(12/5)*s^2 := by
    have ha := phase_jump_bound w hw hm (competitionBase j)
    have hb : |-s*phaseJump w (competitionBase j)| ≤ 9/50 := by
      rw [abs_mul,abs_neg,abs_of_nonneg hs]
      nlinarith [mul_le_mul hs' ha (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1/100)]
    have hsq : (phaseJump w (competitionBase j))^2 ≤ 4 := by
      nlinarith [(abs_le.mp ha).1,(abs_le.mp ha).2]
    have hmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
    nlinarith [exp_small_quadratic (-s*phaseJump w (competitionBase j)) hb]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hl j) (hn j))
  have he : (∑ j,R j*(-s*phaseJump w (competitionBase j)+(12/5)*s^2)) =
      -s*competitionGenerator N V (1/500000000) (1/10) r d w.obs+(12/5)*s^2*(∑ j,R j) := by
    unfold competitionGenerator
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hz : R j=0
    · change R j*_ = _* (R j*_)+_*R j
      simp only [hz,zero_mul,mul_zero,add_zero]
    · have hj := phase_actual_jump w N (competitionBase j)
        (competition_rate_support N V (1/500000000) (1/10) r d j hz)
      change w.obs (competitionNext N j)-w.obs N=_ at hj
      rw [hj]
      ring
  rw [he] at hsum
  have hgen := mul_le_mul_of_nonneg_left (phase_generator_lower w hw N V r d hV hr hr' hd hd' hc) hs
  have htotal := mul_le_mul_of_nonneg_left ht (show 0 ≤ (12/5)*s^2 by positivity)
  rw [phase_exponential_identity]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  dsimp [R] at *
  nlinarith

end
end FiniteCopyReactor
