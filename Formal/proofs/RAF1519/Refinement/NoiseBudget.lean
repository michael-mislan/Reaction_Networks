import proofs.RAF1519.Refinement.QuantitativeStock

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

def intervalFailureAt {n : ℕ} (r d : Fin n → ℝ) (k : Fin n → Fin n → ℝ)
    (V ε : ℝ) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop) :
    Set (ℕ → JumpState (MolecularState n) (CountChannel n)) :=
  {z | ∃ l s, 0 ≤ s ∧
    s ≤ min (z (l+1)).2.2 (4-prefixElapsed l (Preorder.frestrictLe l z)) ∧
    ε ≤ |coordinateWithin (molecularRate r d k V)
      (molecularIncrement r d k V p) (countCorridor V) 4 stop z l s|}

theorem molecular_coordinate_budget {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ ε : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j=k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hlarge : 40/ε ≤ V)
    (N : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV N
      (intervalFailureAt r d k V ε p stop) ≤
      2*ENNReal.ofReal (Real.exp (-(361/5120000)*V*ε^2/(1+Δ))) := by
  let a : ℝ := (19/20)*ε
  let θ : ℝ := V*a/(6400*(1+Δ))
  have hθ : 0 ≤ θ := by dsimp [θ,a]; positivity
  have hs : θ*(2/V) ≤ 1 := by
    have he : θ*(2/V)=a/(3200*(1+Δ)) := by dsimp [θ]; field_simp; ring
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    dsimp [a]
    linarith
  have hres : a+2/V ≤ ε := by
    have hm := (div_le_iff₀ hε).mp hlarge
    have hj : 2/V ≤ ε/20 := by apply (div_le_iff₀ hV).mpr; nlinarith
    dsimp [a]; linarith
  have hb := molecular_interval_tail hn r d k V Δ θ 4 a hr hd hk hV hΔ hsym hdegree
    hθ hs (by norm_num) N p stop hstop
  have he : -θ*a+θ^2*(800*(1+Δ)/V)*4 = -(361/5120000)*V*ε^2/(1+Δ) := by
    have hq : 1+Δ ≠ 0 := by positivity
    dsimp [θ,a]
    field_simp
    ring
  rw [he] at hb
  apply (measure_mono ?_).trans hb
  intro z hz
  obtain ⟨l,s,hs0,hsh,hc⟩ := hz
  exact ⟨l,s,hs0,hsh,hres.trans hc⟩

theorem relaxed_exponent_margin (V Δ : ℝ) (hV : 0 < V) (hΔ : 0 ≤ Δ) :
    -(361/5120000)*V*(relaxedTolerance Δ)^2/(1+Δ) ≤
      -V/(2000000000000*(1+Δ)^3) := by
  have hq : 0 < 1+Δ := by positivity
  have he : -(361/5120000)*V*(relaxedTolerance Δ)^2/(1+Δ) =
      -(361/512000000000000)*(V/(1+Δ)^3) := by
    unfold relaxedTolerance
    field_simp
    ring
  have he' : -V/(2000000000000*(1+Δ)^3)=-(1/2000000000000)*(V/(1+Δ)^3) := by
    field_simp
  rw [he,he']
  have hp : 0 ≤ V/(1+Δ)^3 := by positivity
  nlinarith

end
end RAF1519.Refinement
