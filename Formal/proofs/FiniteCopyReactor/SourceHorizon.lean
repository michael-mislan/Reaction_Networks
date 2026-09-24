import proofs.FiniteCopyReactor.ReturnedTotals

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

/-- A nonempty restart set at every integer scale, including the effective sizing rule. -/
theorem all_free_restart (V : ℕ) : Restart V ![0,0,V,0,0,0] := by
  have ha : uCount ![0,0,V,0,0,0]=(V:ℝ) := by
    rw [uCount_expansion]
    norm_num
    rfl
  have hb : wCount ![0,0,V,0,0,0]=(V:ℝ) := by
    rw [wCount_expansion]
    norm_num
    rfl
  have hs : stockInteger ![0,0,V,0,0,0]=40*V := by simp [stockInteger]
  unfold Restart
  rw [ha,hb,hs]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals nlinarith [Nat.cast_nonneg (α := ℝ) V]

theorem full_source_hundred_cycles (N : Counts) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hN : Restart 200000000000 N) :
    ENNReal.ofReal (99/100:ℝ) ≤
      fullHistoryKernel (returnedHistoryStep N 200000000000 r d (by norm_num) (by linarith) hd policy)
        100 [] (returnedFinal 200000000000 100) := by
  have hb := hundred_cycle_error_budget
  have hl : (99/100:ℝ) ≤ 1-(100:ℝ)*oneCycleError 200000000000 := by linarith
  exact (ENNReal.ofReal_le_ofReal hl).trans (full_returned_history_success N 200000000000 r d
    (by norm_num) hr hr' hd hd' policy (by norm_num) hN 100)

theorem full_source_effective_volume (m : ℕ) (δ : ℝ) (hδ : 0 < δ) (N : Counts) (r d : ℝ)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (policy : ReturnedHistory → Intervention) (hN : Restart (sufficientVolume m δ) N) :
    ENNReal.ofReal (1-δ) ≤
      fullHistoryKernel (returnedHistoryStep N (sufficientVolume m δ) r d
        (by have hv : 200000000000 ≤ sufficientVolume m δ := le_max_left _ _; exact_mod_cast (show 0 < sufficientVolume m δ by omega))
        (by linarith) hd policy) m [] (returnedFinal (sufficientVolume m δ) m) := by
  have hs : 200000000000 ≤ sufficientVolume m δ := le_max_left _ _
  have hb := sufficient_volume_error m δ hδ
  have hl : 1-δ ≤ 1-(m:ℝ)*oneCycleError (sufficientVolume m δ) := by linarith
  exact (ENNReal.ofReal_le_ofReal hl).trans (full_returned_history_success N (sufficientVolume m δ) r d
    (by exact_mod_cast (show 0 < sufficientVolume m δ by omega)) hr hr' hd hd' policy hs hN m)

end
end FiniteCopyReactor
