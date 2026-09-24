import proofs.FiniteCopyReactor.PhaseKernel
import proofs.FiniteCopyReactor.PhaseWindow

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

def LowFree (V : ℕ) : Set (BoxCounts V) :=
  {X | resourceGood (boxCounts X) V ∧ (boxCounts X 2:ℝ) ≤ (V:ℝ)/1000}

theorem low_free_indicator (V : ℕ) (N : BoxCounts V) :
    FiniteKernel.eventIndicator (LowFree V) N ≤
      Real.exp ((V:ℝ)/1000000000)*phaseTest V (1/1000000) (phaseWeights (3000*(V:ℝ)) 0) N := by
  by_cases h : N ∈ LowFree V
  · rw [FiniteKernel.eventIndicator,if_pos h]
    simp only [phaseTest,if_pos h.1,phaseWeights,PhaseWeights.obs,one_mul,zero_mul,add_zero]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    linarith [h.2]
  · rw [FiniteKernel.eventIndicator,if_neg h]
    unfold phaseTest
    split_ifs <;> positivity

theorem phase_discrete_probability (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (n : ℕ) (hn : 89*V ≤ n) (hn' : n ≤ 91*V) (N : BoxCounts V)
    (hstock : (V:ℝ)/20 ≤ weightedCount (boxCounts N)) :
    (materialKernel V r d hV (by linarith) hr' hd hd').steps n
      (FiniteKernel.eventIndicator (LowFree V)) N ≤ Real.exp (-(V:ℝ)/10000000000) := by
  let P := materialKernel V r d hV (by linarith) hr' hd hd'
  have hi := P.steps_mono (low_free_indicator V) n N
  rw [P.steps_scale] at hi
  have ht := phase_steps_transfer V r d (1/1000000) hV hr hr' hd hd'
    (by norm_num) (by norm_num) n N
  have hinit : phaseTest V (1/1000000) (phaseWeights (3000*(V:ℝ)) n) N ≤
      Real.exp (-(V:ℝ)/700000000) := by
    unfold phaseTest
    split_ifs
    · apply Real.exp_le_exp.mpr
      have hh := phase_window_stock V hV n hn hn' (boxCounts N)
      linarith
    · exact (Real.exp_pos _).le
  have hh := hi.trans (mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)) (Real.exp_pos _).le)
  rw [← mul_assoc,← Real.exp_add,← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hnr : (n:ℝ) ≤ 91*V := by exact_mod_cast hn'
  nlinarith

end
end FiniteCopyReactor
