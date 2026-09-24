import proofs.RAF1519.Refinement.CountStockFence
import proofs.RAF1519.Refinement.Pulse

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem count_ready_return {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
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
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    Ready (1/100) (fun s => countPath V z 4 (i,s)) := by
  have ha := material_return_four r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K hK false i
  have hb := material_return_four r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K hK true i
  have hd4 := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD
    K 4 (by norm_num) le_rfl hK i
  have hdret := (intermediate_envelope_margins 4 _ (by norm_num) hd4).2 rfl
  have hy4 := count_stock_fence r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY
    K 4 (by norm_num) le_rfl hK i
  have hyret := stock_recovered_of_fence 4 _ (by norm_num) hy4
  simp only [countMaterial,materialWeight,← materialA_weighted] at ha
  simp only [countMaterial,materialWeight,← materialB_weighted] at hb
  change 58/1000 < stock (fun s => countPath V z 4 (i,s)) at hyret
  obtain ⟨haL,haU⟩ := abs_lt.mp ha
  obtain ⟨hbL,hbU⟩ := abs_lt.mp hb
  refine ⟨?_,⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩,by linarith,?_⟩
  · intro s
    exact div_nonneg (Nat.cast_nonneg _) hV.le
  · dsimp only
    linarith

end
end RAF1519.Refinement
