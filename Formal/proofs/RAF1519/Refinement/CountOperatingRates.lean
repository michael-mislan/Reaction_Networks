import proofs.RAF1519.Refinement.CountPhaseOutput

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

theorem count_inventory_from_stock (V : ℝ) (hV : 0 < V) {n : ℕ}
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (t : ℝ) (i : Fin n)
    (hY : 58/1000 < countStock V z t i) :
    4/100 < ProductiveRecovery.inventory (free (fun s => countPath V z t (i,s))) := by
  have hc : ∀ s, 0 ≤ countPath V z t (i,s) := fun s => div_nonneg (Nat.cast_nonneg _) hV.le
  have hf : ProductiveRecovery.Nonneg (free (fun s => countPath V z t (i,s))) := by
    intro p
    fin_cases p <;> simpa [free] using hc _
  have hi := ProductiveRecovery.inventory_lower _ hf
  change (5/7)*countStock V z t i ≤ _ at hi
  linarith

theorem count_service_rate {n : ℕ} (r d : Fin n → ℝ)
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
    (K : ℕ) (hK : 4 < prefixElapsed K (Preorder.frestrictLe K z))
    (t : ℝ) (ht : 0 ≤ t) (ht4 : t ≤ 4) (i : Fin n) :
    service (d i) (1/100) (1/100) (fun s => countPath V z t (i,s)) ≤ 448816/10000000 := by
  have hs := material_no_exit r d k V Δ hV hΔ hk hsym hdegree z hh hc hnoise h0
  have hcoord := countPath_coordinate_bound V hV z (fun j => (hh j).le) hs K t ht ht4 (ht4.trans_lt hK)
  have hmid := intermediate_time_bound r d k V Δ hV hΔ hd hk hsym hdegree z hh hc hnoise h0 hD
    K t ht ht4 (ht4.trans_lt hK) i
  exact service_rate_bound (d i) _ (hd i).2 (fun s => (hcoord (i,s)).1) (hcoord (i,2)).2
    (intermediate_envelope_margins t _ ht hmid).1.le

end
end RAF1519.Refinement
