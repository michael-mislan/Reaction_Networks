import proofs.FiniteReservoir.ResidencePhase

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical

def LowFreeActive (V M : ℕ) : Set (BoxState V M) :=
  {X | residenceActive V X.1 ∧ (boxCounts X.1 2:ℝ) ≤ (V:ℝ)/1000}

theorem residence_free_indicator (V M : ℕ) (N : BoxState V M) :
    FiniteKernel.eventIndicator (LowFreeActive V M) N ≤
      Real.exp ((V:ℝ)/1000000000)*residencePhaseTest V M (1/1000000) (phaseWeights (3000*(V:ℝ)) 0) N := by
  by_cases h : N ∈ LowFreeActive V M
  · rw [FiniteKernel.eventIndicator,if_pos h]
    simp only [residencePhaseTest,if_pos h.1,phaseWeights,PhaseWeights.obs,one_mul,zero_mul,add_zero]
    rw [← Real.exp_add]
    apply Real.one_le_exp_iff.mpr
    linarith [h.2]
  · rw [FiniteKernel.eventIndicator,if_neg h]
    unfold residencePhaseTest
    split_ifs <;> positivity

theorem residence_free_window (V M : ℕ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) 
    (n : ℕ) (hn : 89*V ≤ n) (hn' : n ≤ 91*V) (N : BoxState V M) :
    (residenceKernel V M p hV).steps n
      (FiniteKernel.eventIndicator (LowFreeActive V M)) N ≤ Real.exp (-(V:ℝ)/10000000000) := by
  let R := residenceKernel V M p hV
  have hi := R.steps_mono (residence_free_indicator V M) n N
  rw [R.steps_scale] at hi
  have ht := residence_phase_steps V M p (1/1000000) hV
    (by norm_num) (by norm_num) n N
  have hinit : residencePhaseTest V M (1/1000000) (phaseWeights (3000*(V:ℝ)) n) N ≤
      Real.exp (-(V:ℝ)/700000000) := by
    unfold residencePhaseTest
    split_ifs with hc
    · apply Real.exp_le_exp.mpr
      have hh := phase_window_stock V hV n hn hn' (boxCounts N.1)
      linarith [hc.2]
    · exact (Real.exp_pos _).le
  have hh := hi.trans (mul_le_mul_of_nonneg_left
    (ht.trans (mul_le_mul_of_nonneg_left hinit (Real.exp_pos _).le)) (Real.exp_pos _).le)
  rw [← mul_assoc,← Real.exp_add,← Real.exp_add] at hh
  apply hh.trans
  apply Real.exp_le_exp.mpr
  have hnr : (n:ℝ) ≤ 91*V := by exact_mod_cast hn'
  nlinarith

/-- Uniform in the actual initial state: inactive states contribute zero.
Composition extends the short-window estimate to every later clock. -/
theorem residence_free_after_burnin (V M : ℕ) (p : Parameters M)
    (hV : 0 < (V:ℝ)) 
    (n : ℕ) (hn : 90*V ≤ n) (N : BoxState V M) :
    (residenceKernel V M p hV).steps n
      (FiniteKernel.eventIndicator (LowFreeActive V M)) N ≤ Real.exp (-(V:ℝ)/10000000000) := by
  let R := residenceKernel V M p hV
  have hh := R.steps_mono
    (residence_free_window V M p hV (90*V) (by omega) (by omega)) (n-90*V) N
  rw [R.steps_const,← steps_comp] at hh
  simpa only [Nat.sub_add_cancel hn] using hh

end
end FiniteReservoir
