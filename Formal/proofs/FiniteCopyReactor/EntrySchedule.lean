import proofs.FiniteCopyReactor.Entry
import proofs.RandomViability.BindingCappedSchedule

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem seeded_clock_growth (V : ℕ) (hV : 0 < (V:ℝ)) :
    (101/20:ℝ) ≤ (1+(5/8)/(3000*(V:ℝ)))^(8100*V) := by
  have h := one_add_mul_le_pow
    (show (-2:ℝ) ≤ (5/8)/(3000*(V:ℝ)) by
      have hh : 0 ≤ (5/8)/(3000*(V:ℝ)) := by positivity
      linarith) (300*V)
  have he : ((300*V:ℕ):ℝ)*((5/8)/(3000*(V:ℝ))) = 1/16 := by
    push_cast
    field_simp
    norm_num
  rw [he] at h
  norm_num at h
  have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 17/16) h 27
  rw [show 8100*V = (300*V)*27 by omega, pow_mul]
  exact (by norm_num : (101/20:ℝ) ≤ (17/16)^27).trans hp

def routineEntryKernel (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    FiniteKernel (BoxCounts V) :=
  (competitionEntryModel V ((3/50)*(V:ℝ)) (1/500000000) (1/10) r d hV
    (by norm_num) (by norm_num) (by linarith) hd).uniformize (3000*(V:ℝ))
    (by positivity) (fun N => competition_entry_total_bound V ((3/50)*(V:ℝ))
      (1/500000000) (1/10) r d hV (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by linarith) (by linarith) hd (by linarith) N)

theorem seeded_discrete_transfer (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) :
    (routineEntryKernel V r d hV hr hr' hd hd').steps (8100*V)
      (entryTest V ((3/50)*(V:ℝ)) (1/1000)) N ≤
        entryTest V ((3/50)*(V:ℝ)) (101/20000) N := by
  apply steps_capped_target (routineEntryKernel V r d hV hr hr' hd hd')
    (entryTest V ((3/50)*(V:ℝ))) (101/20000) (1+(5/8)/(3000*(V:ℝ)))
    (1/1000) (101/20000) (by norm_num)
    (le_add_of_nonneg_right (by positivity))
    (by norm_num) (by norm_num) (entryTest_antitone V ((3/50)*(V:ℝ)))
  · intro s hs hsc X
    unfold routineEntryKernel
    apply FiniteCopyReactor.entry_step_transfer V ((3/50)*(V:ℝ)) r d s
      (min (101/20000) ((1+(5/8)/(3000*(V:ℝ)))*s)) (3000*(V:ℝ)) hV hr hr' hd hd'
      le_rfl hs (by linarith) (min_le_right _ _) (by positivity)
  · norm_num
  · have h := seeded_clock_growth V hV
    linarith

end
end FiniteCopyReactor
