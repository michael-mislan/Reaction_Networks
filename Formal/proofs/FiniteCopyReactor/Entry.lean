import proofs.FiniteCopyReactor.StockExponential
import proofs.RandomViability.BindingCompetitionEntryKernel

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical

theorem corridor_stock_exponential (N : Counts) (V : ℕ) (r d s : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hcor : resourceGood N V)
    (hY : weightedCount N ≤ (3/50)*(V:ℝ)) (hs : 0 ≤ s) (hs' : s ≤ 1/100) :
    competitionGenerator N V (1/500000000) (1/10) r d (fun X => Real.exp (-s*weightedCount X)) ≤
      Real.exp (-s*weightedCount N)*(-(5/8)*s*weightedCount N) := by
  have ha : A (concentration N V) = uCount N/(V:ℝ) := by
    rw [uCount_expansion]
    dsimp [A,concentration]
    ring
  have hb : B (concentration N V) = wCount N/(V:ℝ) := by
    rw [wCount_expansion]
    dsimp [B,concentration]
    ring
  have hc (i : Fin 6) : (N i:ℝ)/(V:ℝ) ≤ 11/10 :=
    (div_le_iff₀ hV).mpr (resource_count_cap N V hcor i)
  rw [← generator_projection]
  apply stock_exponential_drift N V r d s hV hr hr' hd hd'
  · rw [ha]
    exact (le_div_iff₀ hV).mpr hcor.1
  · rw [hb]
    exact (le_div_iff₀ hV).mpr hcor.2.2.1
  · rw [normalized_stock]
    exact (div_le_iff₀ hV).mpr hY
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hs
  · exact hs'

/-- One actual uniformized C2 entry step; no success probability is a premise. -/
theorem entry_step_transfer (V : ℕ) (H r d s t q : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 19 ≤ r) (hr' : r ≤ 21)
    (hd : 0 ≤ d) (hd' : d ≤ 1/25) (hH : H ≤ (3/50)*(V:ℝ))
    (hs : 0 ≤ s) (hs' : s ≤ 1/100) (ht : t ≤ (1+(5/8)/q)*s)
    (hq : 0 < q)
    (hbound : ∀ N, (competitionEntryModel V H (1/500000000) (1/10) r d hV
      (by norm_num) (by norm_num) (by linarith) hd).total N ≤ q)
    (N : BoxCounts V) :
    ((competitionEntryModel V H (1/500000000) (1/10) r d hV
      (by norm_num) (by norm_num) (by linarith) hd).uniformize q hq hbound).step
      (entryTest V H s) N ≤ entryTest V H t N := by
  rw [FiniteJumpModel.uniformize_step]
  by_cases h : entryActive V H N
  · have hg := (competition_entry_generator_inside V H (1/500000000) (1/10) r d s hV
      (by norm_num) (by norm_num) (by linarith) hd N h).trans
      (corridor_stock_exponential (boxCounts N) V r d s hV hr hr' hd hd' h.1
        (h.2.le.trans hH) hs hs')
    have hdiv := div_le_div_of_nonneg_right hg hq.le
    simp only [entryTest, if_pos h]
    calc
      _ ≤ Real.exp (-s*weightedCount (boxCounts N)) *
          (1+(-(5/8)*s*weightedCount (boxCounts N))/q) := by
        calc
          _ ≤ Real.exp (-s*weightedCount (boxCounts N)) +
              Real.exp (-s*weightedCount (boxCounts N)) *
                (-(5/8)*s*weightedCount (boxCounts N))/q := add_le_add le_rfl hdiv
          _ = _ := by ring
      _ ≤ Real.exp (-s*weightedCount (boxCounts N)) *
          Real.exp ((-(5/8)*s*weightedCount (boxCounts N))/q) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp ((-(5/8)*s*weightedCount (boxCounts N))/q)]
      _ = Real.exp (-((1+(5/8)/q)*s)*weightedCount (boxCounts N)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hm := mul_le_mul_of_nonneg_right ht (weightedCount_nonneg (boxCounts N))
        linarith
  · rw [competition_entry_generator_outside V H (1/500000000) (1/10) r d s hV
      (by norm_num) (by norm_num) (by linarith) hd N h]
    simp only [entryTest, if_neg h, zero_div, add_zero, le_refl]

end
end FiniteCopyReactor
