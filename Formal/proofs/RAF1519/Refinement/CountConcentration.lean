import proofs.RAF1519.Refinement.ExchangeVariance
import proofs.RAF1519.Refinement.CensoredInterval

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

def countCorridor {n : ℕ} (V : ℝ) : Set (MolecularState n) :=
  {N | ∀ q, (N q : ℝ)/V ≤ 11/10}

/-- The physical count law supplies every jump and variance premise of the
    censored concentration theorem. The history stop may encode a first exit. -/
theorem molecular_interval_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V Δ θ T δ : ℝ)
    (hr : ∀ i, 0 ≤ r i ∧ r i ≤ 21) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V) (hΔ : 0 ≤ Δ)
    (hsym : ∀ i j, k i j = k j i) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (hθ : 0 ≤ θ) (hsmall : θ*(2/V) ≤ 1) (hT : 0 ≤ T)
    (initial : MolecularState n) (p : Fin n × Fin 7)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV initial
      {z | ∃ l s, 0 ≤ s ∧
        s ≤ min (z (l+1)).2.2 (T-prefixElapsed l (Preorder.frestrictLe l z)) ∧
        δ+2/V ≤ |coordinateWithin (molecularRate r d k V)
          (molecularIncrement r d k V p) (countCorridor V) T stop z l s|} ≤
      2*ENNReal.ofReal (Real.exp (-θ*δ+θ^2*(800*(1+Δ)/V)*T)) := by
  apply coordinate_interval_tail initial (molecularNext r d k) (molecularRate r d k V)
    (molecularIncrement r d k V p)
    (molecular_rate_nonnegative r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV.le)
    (molecular_total_positive hn r d k V (fun i => (hr i).1) (fun i => (hd i).1) hk hV)
    (countCorridor V) θ (800*(1+Δ)/V) T (2/V) hθ (by positivity) hT (by positivity)
    (fun N a => molecular_increment_bound r d k V hV p N a) _ _ stop hstop δ
  · intro N _ a
    rw [abs_mul,abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left (molecular_increment_bound r d k V hV p N a) hθ).trans hsmall
  · intro N hN
    exact molecular_coordinate_variance r d k V Δ hr hd hk hV hΔ hsym hdegree p N hN

end
end RAF1519.Refinement
