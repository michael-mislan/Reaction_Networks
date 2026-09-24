import proofs.RAF1519.Refinement.MaterialStop

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability

theorem countDriftPrimitive_zero {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 ≤ (z (i+1)).2.2) (K : ℕ) (p : Fin n × Fin 7) :
    countDriftPrimitive r d k V z K p 0 = ((z 0).1 p:ℝ)/V := by
  have he := holdingPrimitive_at_clock (fun i => (z (i+1)).2.2)
    (fun i => ∑ a, molecularRate r d k V (z i).1 a*molecularIncrement r d k V p (z i).1 a)
    hh K 0 (Nat.zero_le K)
  simp only [holdingClock_zero,Finset.range_zero,Finset.sum_empty] at he
  simp only [countDriftPrimitive,he,add_zero]

theorem materialPrimitive_zero {n : ℕ} (b : Bool) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 ≤ (z (i+1)).2.2) (K : ℕ) (i : Fin n) :
    materialPrimitive b r d k V z K 0 i = materialNode b V (z 0).1 i := by
  unfold materialPrimitive materialNode
  simp only [countDriftPrimitive_zero r d k V z hh K]
  rfl

/-- Even the first unsafe state is controlled: the preceding intervals alone
    need to be unstopped. The noise event already includes the zero offset. -/
theorem count_endpoint_noise {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n))
    (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (hc : ∀ i, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hnoise : ∀ p, z ∉ countIntervalFailure r d k V Δ p (materialExit V))
    (K j : ℕ) (hj : j ≤ K) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ 4)
    (hs : ∀ i < j, ¬coordinateStop (countCorridor V) 4 (materialExit V) i (Preorder.frestrictLe i z))
    (p : Fin n × Fin 7) :
    |((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p
      (prefixElapsed j (Preorder.frestrictLe j z))| < countTolerance Δ := by
  have he := count_endpoint_primitive r d k V 4 p (countCorridor V) (materialExit V)
    z hh K j hj hT (fun i _ => hc i) hs
  have hb : |coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p)
      (countCorridor V) 4 (materialExit V) z j| < countTolerance Δ := by
    apply lt_of_not_ge
    intro hcross
    apply hnoise p
    refine ⟨j,0,le_rfl,le_min (hh j) (sub_nonneg.mpr hT),?_⟩
    simpa only [coordinateWithin,mul_zero,sub_zero,ite_self] using hcross
  have heq : ((z j).1 p:ℝ)/V-countDriftPrimitive r d k V z K p
      (prefixElapsed j (Preorder.frestrictLe j z)) =
      coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p)
        (countCorridor V) 4 (materialExit V) z j := by linarith
  rw [heq]
  exact hb

end
end RAF1519.Refinement
