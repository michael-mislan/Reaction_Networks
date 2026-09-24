import proofs.RandomViability.BindingCompetitionEntryKernel
import proofs.RandomViability.BindingEntrySchedule
import proofs.RandomViability.BindingCappedSchedule

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy

theorem competition_entry_step_capped (V : ℕ) (H eps k r delta cap c s q : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000)
    (hcap : cap ≤ 2/25) (hc : c+3*cap ≤ 3/10) (hs : 0 ≤ s) (hsc : s ≤ cap)
    (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q hq hbound).step
      (entryTest V H s) N ≤ entryTest V H (min cap ((1+c/q)*s)) N := by
  have ht : min cap ((1+c/q)*s) ≤ s+(3/10*s-3*s^2)/q := by
    apply (min_le_right _ _).trans
    have hh : c*s ≤ 3/10*s-3*s^2 := by nlinarith
    have hd := div_le_div_of_nonneg_right hh hq.le
    rw [show (1+c/q)*s = s+c*s/q by ring]
    exact add_le_add le_rfl hd
  have h := competition_entry_step_transfer V H eps k r delta s (min cap ((1+c/q)*s)) q hV
    heps heps1 hk hk1 hr hr1 hd hd1 hH hs (hsc.trans hcap) ht hq hbound N
  have he : Real.exp (-(14/25)*eps*V*s/q) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have hp : 0 ≤ (14/25)*eps*(V:ℝ)*s/q := by positivity
    calc
      _ = -((14/25)*eps*(V:ℝ)*s/q) := by ring
      _ ≤ 0 := neg_nonpos.mpr hp)
  have hh := mul_le_mul_of_nonneg_right he (entryTest_nonneg V H (min cap ((1+c/q)*s)) N)
  exact h.trans (by simpa only [one_mul] using hh)

theorem competition_entry_hundred_clock_transfer (V q : ℕ) (H eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000) (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q (by exact_mod_cast hq) hbound).steps
      (100*q) (entryTest V H (1/40000)) N ≤ entryTest V H (2/25) N := by
  let P := (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q (by exact_mod_cast hq) hbound
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have first (X : BoxCounts V) : P.steps (90*q) (entryTest V H (1/40000)) X ≤
      entryTest V H (1/20) X := by
    apply steps_capped_target P (entryTest V H) (1/20) (1+(3/20)/(q:ℝ)) (1/40000) (1/20)
      (by norm_num) (by have h := div_nonneg (by norm_num : (0:ℝ) ≤ 3/20) hq'.le; linarith)
      (by norm_num) (by norm_num) (entryTest_antitone V H)
    · intro s hs hsc x
      exact competition_entry_step_capped V H eps k r delta (1/20) (3/20) s q hV heps heps1 hk hk1 hr hr1 hd hd1
        hH (by norm_num) (by norm_num) hs hsc hq' hbound x
    · norm_num
    · have h := ninety_clock_growth q hq
      nlinarith
  have second (X : BoxCounts V) : P.steps (10*q) (entryTest V H (1/20)) X ≤
      entryTest V H (2/25) X := by
    apply steps_capped_target P (entryTest V H) (2/25) (1+(3/50)/(q:ℝ)) (1/20) (2/25)
      (by norm_num) (by have h := div_nonneg (by norm_num : (0:ℝ) ≤ 3/50) hq'.le; linarith)
      (by norm_num) (by norm_num) (entryTest_antitone V H)
    · intro s hs hsc x
      exact competition_entry_step_capped V H eps k r delta (2/25) (3/50) s q hV heps heps1 hk hk1 hr hr1 hd hd1
        hH (by norm_num) (by norm_num) hs hsc hq' hbound x
    · norm_num
    · have h := ten_clock_growth q hq (3/50) (by norm_num)
      nlinarith
  change P.steps (100*q) _ N ≤ _
  rw [show 100*q = 10*q+90*q by omega,steps_comp]
  exact (P.steps_mono first (10*q) N).trans (second N)

end
end RandomViability.Binding
