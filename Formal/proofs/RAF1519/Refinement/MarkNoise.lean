import proofs.RAF1519.Refinement.MarkNoiseScale

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal
set_option maxHeartbeats 30000

def markIntervalFailure {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V : ℝ) (i : Fin n) (m : PhysicalMark)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop) :
    Set (ℕ → JumpState (MolecularState n) (CountChannel n)) :=
  {z | ∃ l s, 0 ≤ s ∧
    s ≤ min (z (l+1)).2.2 (4-prefixElapsed l (Preorder.frestrictLe l z)) ∧
    markTolerance ≤ |coordinateWithin (molecularRate r d k V)
      (markIncrement V i m) {N | materialSafe V N} 4 stop z l s|}

theorem molecular_mark_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V)
    (initial : MolecularState n) (i : Fin n) (m : PhysicalMark)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V hr (fun i => (hd i).1) hk hV initial
      (markIntervalFailure r d k V i m stop) ≤
      2*ENNReal.ofReal (Real.exp (-V/160000000)) := by
  by_cases hlarge : 80000 ≤ V
  · have ht := mark_tilt_small V hV
    have hb := molecular_mark_interval_tail hn r d k V (markTilt V) 4 markThreshold
      hr hd hk hV ht.1 ht.2 (by norm_num) initial i m stop hstop
    apply le_trans (le_trans (measure_mono ?_) hb)
    · exact mul_le_mul_right
        (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (mark_exponent_margin V hV))) 2
    · intro z hz
      obtain ⟨l,s,hs,hsh,hc⟩ := hz
      exact ⟨l,s,hs,hsh,(mark_interval_reserve V hV hlarge).trans hc⟩
  · exact prob_le_one.trans (mark_small_volume_trivial V (le_of_not_ge hlarge))

theorem molecular_all_mark_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V)
    (initial : MolecularState n)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V hr (fun i => (hd i).1) hk hV initial
      (⋃ p : Fin n × PhysicalMark, markIntervalFailure r d k V p.1 p.2 stop) ≤
      10*n*ENNReal.ofReal (Real.exp (-V/160000000)) := by
  calc
    _ ≤ ∑ p : Fin n × PhysicalMark,
        molecularLaw hn r d k V hr (fun i => (hd i).1) hk hV initial
          (markIntervalFailure r d k V p.1 p.2 stop) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin n × PhysicalMark, 2*ENNReal.ofReal (Real.exp (-V/160000000)) :=
      Finset.sum_le_sum (fun p _ => molecular_mark_tail hn r d k V hr hd hk hV
        initial p.1 p.2 stop hstop)
    _ = _ := by
      have hc : Fintype.card PhysicalMark = 5 := by decide
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,hc,
        nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]
      ring

end
end RAF1519.Refinement
