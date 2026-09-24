import proofs.RAF1519.Refinement.CountPhaseBinding

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 50000

/-- Actual free-X output at every physical time in the collection window, from
    the single pathwise noise event. No union over fixed-time events is used. -/
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
    7/1000 < countPath V z t (i,2) := by
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
  have hout := phase_window_lower k hk hsym Δ (countTolerance Δ) (58/1000) hΔ
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
      have hrdy := (stock_recovered_of_fence a _ ha hstock).le
      dsimp [X]
      rw [add_zero,phaseDot_stock (fun s => countPath V z a (j,s))]
      exact hrdy)
    (fun s hs j p => count_phase_path_drift r d k V hV hr hd hsym z hh0 hsafe K (a+s)
      (htime s ⟨hs.1,hs.2.le⟩).1 (htime s ⟨hs.1,hs.2.le⟩).2
      ((htime s ⟨hs.1,hs.2.le⟩).2.trans_lt hK) j p) i
  have he : 8*(1+Δ)*countTolerance Δ = 8/100000 := by
    unfold countTolerance
    have hn : 1+Δ ≠ 0 := by positivity
    field_simp
  rw [he] at hout
  change 58/1000/8-8/100000 ≤ countPath V z (a+1/28) (i,phaseSpecies 0) at hout
  have haend : a+1/28=t := by dsimp [a]; ring
  rw [haend] at hout
  change 58/1000/8-8/100000 ≤ countPath V z t (i,2) at hout
  linarith

end
end RAF1519.Refinement
