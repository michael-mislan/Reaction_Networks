import proofs.RAF1519.Refinement.IntermediateTime

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem countPath_free_material_lower {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hd : ∀ i, 1/50 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (hD : ∀ i, ((z 0).1 (i,6):ℝ)/V ≤ 1101/100000)
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (i : Fin n) :
    94878/100000 ≤ ProductiveRecovery.A (free (fun s => countPath V z T (i,s))) ∧
    94878/100000 ≤ ProductiveRecovery.B (free (fun s => countPath V z T (i,s))) := by
  have ha := material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K T hT0 hT hK false i
  have hb := material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K T hT0 hT hK true i
  change |weightedCoordinate weightA (fun s => countPath V z T (i,s))-1| ≤ _ at ha
  change |weightedCoordinate weightB (fun s => countPath V z T (i,s))-1| ≤ _ at hb
  rw [← materialA_weighted] at ha
  rw [← materialB_weighted] at hb
  have he : Real.exp (-T) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hT0)
  have hda := (abs_le.mp ha).1
  have hdb := (abs_le.mp hb).1
  have hdi := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD K T hT0 hT hK i
  have hbound := (intermediate_envelope_margins T _ hT0 hdi).1
  exact free_material_from_augmented _ (by linarith) (by linarith) hbound.le

end
end RAF1519.Refinement
