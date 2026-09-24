import proofs.RAF1519.Refinement.MaterialFirstExit

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 40000

theorem countPath_noise_after_material_no_exit {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (hsafe : ∀ j, prefixElapsed j (Preorder.frestrictLe j z) ≤ 4 → materialSafe V (z j).1)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hT : t ≤ 4)
    (hK : t < prefixElapsed K (Preorder.frestrictLe K z)) (p : Fin n × Fin 7) :
    |countPath V z t p-countDriftPrimitive r d k V z K p t| < countTolerance Δ := by
  have hh0 := fun i => (hh i).le
  have hi := countPathIndex_spec z hh0 K t ht hK
  have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh0
  have hj4 := hi.2.1.trans hT
  have hstop : ∀ q, prefixElapsed q (Preorder.frestrictLe q z) < 4 →
      ¬coordinateStop (countCorridor V) 4 (materialExit V) q (Preorder.frestrictLe q z) := by
    intro q hq
    exact material_unstopped V hV z q hq (fun l hl => hsafe l ((hm hl).trans hq.le))
  by_cases hj : prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z) < 4
  · exact countPath_primitive_noise r d k V Δ (materialExit V) z hh0 hc hnoise K t ht hT hK
      (fun q hq => hstop q ((hm hq).trans_lt hj)) p
  · have he : prefixElapsed (countPathIndex z t) (Preorder.frestrictLe (countPathIndex z t) z)=t := by linarith
    have hs : ∀ q < countPathIndex z t,
        ¬coordinateStop (countCorridor V) 4 (materialExit V) q (Preorder.frestrictLe q z) := by
      intro q hq
      exact hstop q ((holdingClock_strictMono _ hh hq).trans_le hj4)
    have hb := count_endpoint_noise r d k V Δ z hh0 hc hnoise K (countPathIndex z t) hi.1.le hj4 hs p
    rw [he] at hb
    exact hb

theorem material_time_bound {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (K : ℕ) (T : ℝ) (hT0 : 0 ≤ T) (hT : T ≤ 4)
    (hK : T < prefixElapsed K (Preorder.frestrictLe K z)) (b : Bool) (i : Fin n) :
    |countMaterial b V z T i-1| ≤ (1/25)*Real.exp (-T)+18/100000 := by
  have hh0 := fun i => (hh i).le
  have heps := (count_tolerance_positive Δ hΔ).le
  have hsafe := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have hpath : ∀ t ∈ Set.Icc 0 T, ∀ q,
      |countMaterial b V z t q-materialPrimitive b r d k V z K t q| ≤ 9*countTolerance Δ := by
    intro t ht q
    exact material_noise_from_coordinates b _ _ _ heps (fun s =>
      (countPath_noise_after_material_no_exit r d k V Δ hV z hh hc hnoise hsafe K t ht.1
        (ht.2.trans hT) (ht.2.trans_lt hK) (q,s)).le)
  have hF := compensated_material_primitive_bound k hk hsym Δ (9*countTolerance Δ) hΔ
    (by positivity) hdegree (countMaterial b V z) (materialPrimitive b r d k V z K)
    (fun t q => 1-countMaterial b V z t q+graphDiffusion k (countMaterial b V z t) q) T (1/25)
    (fun q => (materialPrimitive_continuous b r d k V z K q).continuousOn)
    (fun t ht q => materialPrimitive_right_derivative b r d k V hV.ne' hsym z hh0 K q t ht.1 (ht.2.trans hK))
    (fun q => by rw [materialPrimitive_zero b r d k V z hh0 K]; exact h0 b q)
    (fun _ _ _ => rfl) (fun t ht q => hpath t ⟨ht.1,ht.2.le⟩ q) T ⟨hT0,le_rfl⟩ i
  have hb := material_observed_from_primitive _ _ _ _ _ _ hF (hpath T ⟨hT0,le_rfl⟩ i)
  have he : (2*Δ+1)*(9*countTolerance Δ)+9*countTolerance Δ = 18/100000 := by
    unfold countTolerance
    have hn : 1+Δ ≠ 0 := by positivity
    field_simp
    ring
  rw [add_assoc,he] at hb
  exact hb

theorem material_time_four_margin : (1/25:ℝ)*Real.exp (-4)+18/100000 < 1/1000 := by
  have he : 50 ≤ Real.exp 4 := by
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ 4) 8
    norm_num [Finset.sum_range_succ] at h
    linarith
  have hi : Real.exp (-4) ≤ 1/50 := by
    rw [Real.exp_neg,inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos 4)).mpr
    linarith
  linarith

theorem material_return_four {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 < (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (h0 : ∀ b i, |materialNode b V (z 0).1 i-1| ≤ 1/25)
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z)) (b : Bool) (i : Fin n) :
    |countMaterial b V z 4 i-1| < 1/1000 :=
  (material_time_bound r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0 K 4
    (by norm_num) le_rfl hK b i).trans_lt material_time_four_margin

end
end RAF1519.Refinement
