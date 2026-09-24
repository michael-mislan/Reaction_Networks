import proofs.RAF1519.Refinement.StockPath
import proofs.RAF1519.Refinement.CompensatedStockFence

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem count_stock_fence {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hr : ∀ i, 19 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (hY : ∀ i, 12/1000 ≤ stock (concentration V (fun s => (z 0).1 (i,s))))
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    stockFence T-11/200000 ≤ countStock V z T i := by
  have hh0 := fun j => (hh j).le
  have hs := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have hn : ∀ t ∈ Set.Icc 0 T, ∀ j,
      |countStock V z t j-stockPrimitive r d k V z K t j| ≤ (11/2)*countTolerance Δ := by
    intro t ht j
    exact stock_noise_from_coordinates _ _ _ (count_tolerance_positive Δ hΔ).le (fun s =>
      (countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hs K t ht.1
        (ht.2.trans hT) (ht.2.trans_lt hK) (j,s)).le)
  have hb := compensated_stock_fence k hk hsym Δ hΔ hdegree (countStock V z)
    (stockPrimitive r d k V z K)
    (fun t j => stock (countDrift (r j) (d j) (1/100) (1/100) V (fun s => countPath V z t (j,s)))+
      graphDiffusion k (countStock V z t) j) T
    (fun j => (stockPrimitive_continuous r d k V z K j).continuousOn)
    (fun t ht j => stockPrimitive_right_derivative r d k V hV.ne' hsym z hh0 K j t ht.1 (ht.2.trans hK))
    (fun j => by rw [stockPrimitive_zero r d k V z hh0 K]; exact hY j)
    (fun t ht j => hn t ⟨ht.1,ht.2.le⟩ j) (by
      intro t ht j hsmall
      have hf := countPath_free_material_lower r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD K t ht.1
        (ht.2.le.trans hT) (ht.2.trans hK) j
      have hg := count_guarded_growth (r j) (d j) V (fun s => countPath V z t (j,s))
        (fun s => div_nonneg (Nat.cast_nonneg _) hV.le) (hr j).1 (hr j).2
        (by linarith [(hd j).1]) (hd j).2 hV.le (by linarith [hf.1]) (by linarith [hf.2]) hsmall
      change (2/3)*stock (fun s => countPath V z t (j,s))+_ ≤ _
      dsimp only
      linarith) T ⟨hT0,le_rfl⟩ i
  have he := (abs_le.mp (hn T ⟨hT0,le_rfl⟩ i)).1
  have hm := (stock_noise_allowance Δ hΔ).1
  linarith

theorem stockFence_saturated (t : ℝ) (ht : 11/4 ≤ t) : stockFence t = 59/1000 := by
  have he : (59/1000:ℝ) ≤ (119/10000)*Real.exp (33/20) := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 33/20) 6
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hm := Real.exp_le_exp.mpr (show (33/20:ℝ) ≤ (3/5)*t by linarith)
  exact min_eq_right (he.trans (mul_le_mul_of_nonneg_left hm (by norm_num)))

theorem stock_recovered_of_fence (t Y : ℝ) (ht : 11/4 ≤ t)
    (hY : stockFence t-11/200000 ≤ Y) : 58/1000 < Y := by
  rw [stockFence_saturated t ht] at hY
  linarith

end
end RAF1519.Refinement
