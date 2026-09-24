import proofs.FiniteReservoir.Recovery
import proofs.RandomViability.BindingEntryProbability

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem seeded_after_cutoff (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (n : ℕ) (hn : 8100*V ≤ n) (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1)) :
    (entryKernel V M p hV).steps n
      (FiniteKernel.eventIndicator {X | entryActive V ((3/50)*(V:ℝ)) X.1}) N ≤
        Real.exp (-(3/5000000)*(V:ℝ)) := by
  let P := entryKernel V M p hV
  let H : ℝ := (3/50)*(V:ℝ)
  have hi := P.steps_mono (fun X => entry_indicator_bound V H (1/1000) (by norm_num) X.1) n N
  rw [P.steps_scale] at hi
  have ht := P.steps_mono (seeded_discrete_transfer V M p hV) (n-8100*V) N
  have hdstep (X : BoxState V M) : P.step (entryTest V M H (101/20000)) X ≤
      1*entryTest V M H (101/20000) X := by
    rw [one_mul]
    dsimp [P,H]
    apply entry_step_transfer V M p hV ((3/50)*(V:ℝ)) (101/20000) (101/20000)
      le_rfl (by norm_num) (by norm_num)
    have hh : 0 ≤ (5/8)/(3000*(V:ℝ)) := by positivity
    nlinarith
  have hddec := P.steps_decay_bound (entryTest V M H (101/20000)) 1
    (by norm_num) hdstep (n-8100*V) N
  simp only [one_pow,one_mul] at hddec
  have hb : P.steps n (entryTest V M H (1/1000)) N ≤ entryTest V M H (101/20000) N := by
    have hh := ht.trans hddec
    rw [← steps_comp] at hh
    have he : n-8100*V+8100*V=n := by omega
    simpa only [he] using hh
  have hh := hi.trans (mul_le_mul_of_nonneg_left hb (Real.exp_pos ((1/1000)*H)).le)
  apply hh.trans
  by_cases hactive : entryActive V H N.1
  · simp only [entryTest,RandomViability.Binding.entryTest,if_pos hactive]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [H]
    linarith
  · simp only [entryTest,RandomViability.Binding.entryTest,if_neg hactive,mul_zero]
    exact (Real.exp_pos _).le

/-- At time 11/4, mass still below the target without material exit is small.
Material exits are excluded from this event, and must be paid separately. -/
theorem seeded_recovery_deadline (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (N : BoxState V M) (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1)) :
    (entryKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
      (FiniteKernel.eventIndicator {X | entryActive V ((3/50)*(V:ℝ)) X.1}) N ≤
        Real.exp (-(3/5000000)*(V:ℝ))+Real.exp (-(V:ℝ)/2) := by
  have h := poissonized_after_cutoff (entryKernel V M p hV)
    {X | entryActive V ((3/50)*(V:ℝ)) X.1} N ((8250:ℝ≥0)*V) (8100*V)
    (Real.exp (-(3/5000000)*(V:ℝ))) (99/100)
    (Real.exp_pos _).le (by norm_num) (by norm_num)
    (fun n hn => seeded_after_cutoff V M p hV n hn N hstock)
  apply h.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  have hl := Real.one_sub_inv_le_log_of_pos (show (0:ℝ)<99/100 by norm_num)
  norm_num at hl
  have hm := mul_le_mul_of_nonneg_left hl hV.le
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_natCast,
    NNReal.coe_ofNat]
  nlinarith

end
end FiniteReservoir
