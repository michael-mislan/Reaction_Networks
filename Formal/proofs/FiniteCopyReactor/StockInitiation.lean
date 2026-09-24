import proofs.FiniteCopyReactor.StockVariance

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding

theorem interior_growth_with_initiation (r d : ℝ) (c : State) (hc : Nonneg c)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A c) (hB : 9/10 ≤ B c) (hY : Y c ≤ 3/50) :
    (2/3)*Y c+1/1000000000 ≤ Y (field r d c) := by
  obtain ⟨ha,hb,_⟩ := material_to_food c hc
  have hu : 3/4 ≤ c 0 := by linarith
  have hw : 3/4 ≤ c 1 := by linarith
  have huw : (9/16:ℝ) ≤ c 0*c 1 := by
    have h := mul_le_mul hu hw (by norm_num : (0:ℝ) ≤ 3/4) (hc 0)
    nlinarith
  have hi : 1/1000000000 ≤ ((1/500000000)+d*(1/8000000000))*c 0*c 1 := by
    have he := mul_nonneg (mul_nonneg hd (hc 0)) (hc 1)
    nlinarith
  have h := parameterized_drift r d (3/50) c hc hr' hd' hA hB hY
  have hz := mul_nonneg (show 0 ≤ r/5-19/5 by linarith) (hc 5)
  norm_num at h
  linarith [hc 2,hc 3,hc 4]

theorem count_growth_with_initiation (N : Counts) (V r d : ℝ) (hV : 0 < V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (hA : 9/10 ≤ A (concentration N V)) (hB : 9/10 ≤ B (concentration N V))
    (hY : Y (concentration N V) ≤ 3/50) :
    (2/3)*weightedCount N+V/1000000000 ≤ generator N V r d weightedCount := by
  have hc : Nonneg (concentration N V) := fun i => div_nonneg (Nat.cast_nonneg _) hV.le
  have h := mul_le_mul_of_nonneg_left
    (interior_growth_with_initiation r d (concentration N V) hc hr hr' hd hd' hA hB hY) hV.le
  rw [normalized_stock] at h
  have he : V*((2/3)*(weightedCount N/V)+1/1000000000) =
      (2/3)*weightedCount N+V/1000000000 := by field_simp
  rw [he] at h
  rw [stock_generator_correction N V r d (ne_of_gt hV)]
  have hr0 : 0 ≤ r := by linarith
  exact h.trans (le_add_of_nonneg_right (by positivity))

end
end FiniteCopyReactor
