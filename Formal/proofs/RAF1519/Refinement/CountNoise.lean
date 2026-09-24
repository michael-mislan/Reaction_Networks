import proofs.RAF1519.Refinement.CountNoiseScale

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

def countIntervalFailure {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V Δ : ℝ) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop) :
    Set (ℕ → JumpState (MolecularState n) (CountChannel n)) :=
  {z | ∃ l s, 0 ≤ s ∧
    s ≤ min (z (l+1)).2.2 (4-prefixElapsed l (Preorder.frestrictLe l z)) ∧
    countTolerance Δ ≤ |coordinateWithin (molecularRate r d k V)
      (molecularIncrement r d k V p) (countCorridor V) 4 stop z l s|}

theorem molecular_coordinate_tail_large {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (hlarge : 40/countTolerance Δ ≤ V)
    (initial : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (countIntervalFailure r d k V Δ p stop) ≤
      2*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  have ht := count_tilt_small V Δ hV hΔ
  have hb := molecular_interval_tail hn r d k V Δ (countTilt V Δ) 4 (countThreshold Δ)
    hr hd hk hV hΔ hsym hdegree ht.1 ht.2 (by norm_num) initial p stop hstop
  apply le_trans (le_trans (measure_mono ?_) hb)
  · exact mul_le_mul_right
      (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (count_exponent_margin V Δ hV hΔ))) 2
  · intro z hz
    obtain ⟨l,s,hs,hsh,hc⟩ := hz
    exact ⟨l,s,hs,hsh,(count_interval_reserve V Δ hV hΔ hlarge).trans hc⟩

theorem molecular_coordinate_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (countIntervalFailure r d k V Δ p stop) ≤
      2*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  by_cases hlarge : 40/countTolerance Δ ≤ V
  · exact molecular_coordinate_tail_large hn r d k V Δ hr hd hk hV hΔ hsym hdegree
      hlarge initial p stop hstop
  · exact prob_le_one.trans (count_small_volume_trivial V Δ hΔ (le_of_not_ge hlarge))

theorem molecular_all_coordinate_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (initial : MolecularState n)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      (⋃ p, countIntervalFailure r d k V Δ p stop) ≤
      14*n*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) := by
  calc
    _ ≤ ∑ p, molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
        (countIntervalFailure r d k V Δ p stop) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin n × Fin 7,
        2*ENNReal.ofReal (Real.exp (-V/(200000000000000*(1+Δ)^3))) :=
      Finset.sum_le_sum (fun p _ => molecular_coordinate_tail hn r d k V Δ hr hd hk hV hΔ
        hsym hdegree initial p stop hstop)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_mul,Nat.cast_ofNat]; ring

end
end RAF1519.Refinement
