import proofs.RandomViability.BindingCompetitionEntrySchedule
import proofs.RandomViability.BindingEntryProbability

namespace RandomViability.Binding
noncomputable section
open Classical FiniteCopy
open scoped NNReal

theorem competition_entry_discrete_after_startup (V q : ℕ) (H eps k r delta : ℝ) (hV : 0 < (V:ℝ))
    (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000) (hk : 0 ≤ k) (hk1 : k ≤ 1/8)
    (hr : 18 ≤ r) (hr1 : r ≤ 22) (hdelta : 0 ≤ delta) (hdelta1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000) (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hdelta).total N ≤ q)
    (m : ℕ) (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hdelta).uniformize q (by exact_mod_cast hq) hbound).steps
      (m+100*q) (FiniteKernel.eventIndicator {X | entryActive V H X}) N ≤
      Real.exp (H/40000-((14/25)*eps*V*(2/25)/(q:ℝ))*(m:ℝ)) := by
  let P := (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hdelta).uniformize q (by exact_mod_cast hq) hbound
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hi := P.steps_mono (entry_indicator_bound V H (1/40000) (by norm_num)) (m+100*q) N
  rw [P.steps_scale] at hi
  have ht := P.steps_mono (competition_entry_hundred_clock_transfer V q H eps k r delta hV heps heps1 hk hk1 hr hr1 hdelta hdelta1 hH hq hbound) m N
  have hd (X : BoxCounts V) : P.step (entryTest V H (2/25)) X ≤
      Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))*entryTest V H (2/25) X := by
    apply competition_entry_step_transfer V H eps k r delta (2/25) (2/25) q hV heps heps1 hk hk1 hr hr1 hdelta hdelta1 hH
      (by norm_num) (by norm_num) _ hq' hbound X
    have hpos : 0 ≤ ((3/10:ℝ)*(2/25)-3*(2/25)^2)/(q:ℝ) := by positivity
    linarith
  have hd' := P.steps_decay_bound (entryTest V H (2/25))
    (Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))) (Real.exp_pos _).le hd m N
  have hl := mul_le_mul_of_nonneg_left (entryTest_le_one V H (2/25) (by norm_num) N)
    (pow_nonneg (Real.exp_pos (-(14/25)*eps*V*(2/25)/(q:ℝ))).le m)
  have hb : P.steps m (P.steps (100*q) (entryTest V H (1/40000))) N ≤
      Real.exp (-(14/25)*eps*V*(2/25)/(q:ℝ))^m := by
    exact ht.trans (hd'.trans (by simpa only [mul_one] using hl))
  rw [← steps_comp] at hb
  have hh := mul_le_mul_of_nonneg_left hb (Real.exp_pos ((1/40000)*H)).le
  have result := hi.trans hh
  convert result using 1
  rw [← Real.exp_nat_mul,← Real.exp_add]
  congr 1
  ring

theorem competition_entry_after_cutoff (V q : ℕ) (H eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000) (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (n : ℕ) (hn : 499*q ≤ n) (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q
      (by exact_mod_cast hq) hbound).steps n (FiniteKernel.eventIndicator {X | entryActive V H X}) N ≤
      Real.exp (H/40000-399*((14/25)*eps*V*(2/25))) := by
  have h := competition_entry_discrete_after_startup V q H eps k r delta hV heps heps1 hk hk1
    hr hr1 hd hd1 hH hq hbound (n-100*q) N
  have hn' : n-100*q+100*q=n := by omega
  rw [hn'] at h
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  have hm : 399*(q:ℝ) ≤ (n-100*q:ℕ) := by
    exact_mod_cast (show 399*q ≤ n-100*q by omega)
  have hc : 0 ≤ ((14/25)*eps*(V:ℝ)*(2/25)/(q:ℝ)) := by positivity
  have hh := mul_le_mul_of_nonneg_left hm hc
  have he : ((14/25)*eps*(V:ℝ)*(2/25)/(q:ℝ))*(399*(q:ℝ)) =
      399*((14/25)*eps*V*(2/25)) := by
    field_simp
  rw [he] at hh
  exact h.trans (Real.exp_le_exp.mpr (by linarith))

/-- Physical time 500; startup decay is not charged per export window. -/
theorem competition_entry_deadline (V q : ℕ) (H eps k r delta : ℝ)
    (hV : 0 < (V:ℝ)) (heps : 0 ≤ eps) (heps1 : eps ≤ 1/1000000)
    (hk : 0 ≤ k) (hk1 : k ≤ 1/8) (hr : 18 ≤ r) (hr1 : r ≤ 22)
    (hd : 0 ≤ delta) (hd1 : delta ≤ 3/5) (hH : H ≤ (V:ℝ)/1000) (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).total N ≤ q)
    (N : BoxCounts V) :
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q
      (by exact_mod_cast hq) hbound).poissonized ((q:ℝ≥0)*500)
      (FiniteKernel.eventIndicator {X | entryActive V H X}) N ≤
      Real.exp (H/40000-399*((14/25)*eps*V*(2/25)))+Real.exp (-(q:ℝ)/500000) := by
  have h := poissonized_after_cutoff
    ((competitionEntryModel V H eps k r delta hV heps hk (by linarith) hd).uniformize q
      (by exact_mod_cast hq) hbound) {X | entryActive V H X} N ((q:ℝ≥0)*500) (499*q)
      (Real.exp (H/40000-399*((14/25)*eps*V*(2/25)))) (999/1000)
      (Real.exp_pos _).le (by norm_num) (by norm_num)
      (fun n hn => competition_entry_after_cutoff V q H eps k r delta hV heps heps1 hk hk1
        hr hr1 hd hd1 hH hq hbound n hn N)
  have hc := clock_exponent_bound (q:ℝ) (Nat.cast_nonneg _)
  norm_num only [Nat.cast_mul,Nat.cast_ofNat,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat] at h
  apply h.trans
  apply add_le_add le_rfl
  apply Real.exp_le_exp.mpr
  convert hc using 1
  ring

end
end RandomViability.Binding
