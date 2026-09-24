import proofs.RAF1519.Refinement.RelaxedCorridors
import proofs.RAF1519.Refinement.CountPhaseBinding

namespace RAF1519.Refinement.Relaxed
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 50000

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
    relaxedFence T-11/20000 ≤ countStock V z T i := by
  have hh0 := fun j => (hh j).le
  have hs := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have hn : ∀ t ∈ Set.Icc 0 T, ∀ j,
      |countStock V z t j-stockPrimitive r d k V z K t j| ≤ (11/2)*countTolerance Δ := by
    intro t ht j
    exact stock_noise_from_coordinates _ _ _ (count_tolerance_positive Δ hΔ).le (fun s =>
      (countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hs K t ht.1
        (ht.2.trans hT) (ht.2.trans_lt hK) (j,s)).le)
  have hm := relaxed_stock_margins Δ hΔ
  have hb := compensated_stock_margin k hk hsym Δ ((11/2)*countTolerance Δ)
    (59/5000) (13/250) (11/20) (mul_nonneg (by norm_num) (count_tolerance_positive Δ hΔ).le) (by norm_num) (by norm_num)
    (by norm_num) hdegree (by linarith [hm.1]) (by norm_num) hm.2 (countStock V z)
    (stockPrimitive r d k V z K)
    (fun t j => stock (countDrift (r j) (d j) (1/100) (1/100) V (fun s => countPath V z t (j,s)))+
      graphDiffusion k (countStock V z t) j) T
    (fun j => (stockPrimitive_continuous r d k V z K j).continuousOn)
    (fun t ht j => stockPrimitive_right_derivative r d k V hV.ne' hsym z hh0 K j t ht.1 (ht.2.trans hK))
    (fun j => by rw [stockPrimitive_zero r d k V z hh0 K]; linarith [hY j])
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
  have hmargin := hm.1
  change relaxedFence T ≤ _ at hb
  linarith

theorem stock_recovered_of_fence (t Y : ℝ) (ht : 11/4 ≤ t)
    (hY : relaxedFence t-11/20000 ≤ Y) : 1029/20000 ≤ Y := by
  rw [relaxed_fence_saturated t ht] at hY
  linarith

theorem count_phase_output {n : ℕ} (r d : Fin n → ℝ)
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
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z))
    (t : ℝ) (ht : 3 ≤ t) (ht4 : t ≤ 4) (i : Fin n) :
    901/160000 ≤ countPath V z t (i,2) := by
  let a := t-1/28
  have ha : 11/4 ≤ a := by dsimp [a]; linarith
  have hh0 := fun j => (hh j).le
  have hsafe := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have htime : ∀ s ∈ Set.Icc 0 (1/28), 0 ≤ a+s ∧ a+s ≤ 4 := by
    intro s hs
    dsimp [a]
    constructor <;> linarith [hs.1,hs.2]
  let X := fun s j p => countPath V z (a+s) (j,phaseSpecies p)
  let F := fun s j p => countDriftPrimitive r d k V z K (j,phaseSpecies p) (a+s)
  let v := fun s j p => ∑ b, molecularRate r d k V (z (countPathIndex z (a+s))).1 b*
    molecularIncrement r d k V (j,phaseSpecies p) (z (countPathIndex z (a+s))).1 b
  have hout := phase_window_lower k hk hsym Δ (countTolerance Δ) (1029/20000) hΔ
    (count_tolerance_positive Δ hΔ).le hdegree X F v
    (fun j p => ((countDriftPrimitive_continuous r d k V z K (j,phaseSpecies p)).comp
      (continuous_const.add continuous_id)).continuousOn)
    (fun s hs j p => countPrimitive_shift_derivative r d k V z hh0 K a s
      (htime s ⟨hs.1,hs.2.le⟩).1 ((htime s ⟨hs.1,hs.2.le⟩).2.trans_lt hK) (j,phaseSpecies p))
    (fun _ _ _ _ => div_nonneg (Nat.cast_nonneg _) hV.le)
    (fun s hs j p => (countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hsafe K (a+s)
      (htime s hs).1 (htime s hs).2 ((htime s hs).2.trans_lt hK) (j,phaseSpecies p)).le)
    (by
      intro j
      have hstock := count_stock_fence r d k V Δ hV hΔ hr hd hk hsym hdegree z hh hc hnoise h0 hD hY K a
        (by linarith) (by dsimp [a]; linarith) (by dsimp [a]; linarith) j
      have hrdy := stock_recovered_of_fence a _ ha hstock
      dsimp [X]
      rw [add_zero,phaseDot_stock (fun s => countPath V z a (j,s))]
      exact hrdy)
    (fun s hs j p => count_phase_path_drift r d k V hV hr hd hsym z hh0 hsafe K (a+s)
      (htime s ⟨hs.1,hs.2.le⟩).1 (htime s ⟨hs.1,hs.2.le⟩).2
      ((htime s ⟨hs.1,hs.2.le⟩).2.trans_lt hK) j p) i
  have he : 8*(1+Δ)*countTolerance Δ = 8/10000 := by
    unfold countTolerance relaxedTolerance
    have hn : 1+Δ ≠ 0 := by positivity
    field_simp
  rw [he] at hout
  change 1029/20000/8-8/10000 ≤ countPath V z (a+1/28) (i,phaseSpecies 0) at hout
  have haend : a+1/28=t := by dsimp [a]; ring
  rw [haend] at hout
  change 1029/20000/8-8/10000 ≤ countPath V z t (i,2) at hout
  linarith

end
end RAF1519.Refinement.Relaxed
