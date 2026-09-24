import proofs.RAF1519.Refinement.MarkVariance
import proofs.RAF1519.Refinement.CensoredInterval

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators ENNReal

theorem molecular_mark_interval_tail {n : ℕ} (hn : 0 < n) (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V θ T δ : ℝ)
    (hr : ∀ i, 0 ≤ r i) (hd : ∀ i, 0 ≤ d i ∧ d i ≤ 1/25)
    (hk : ∀ i j, 0 ≤ k i j) (hV : 0 < V)
    (hθ : 0 ≤ θ) (hsmall : θ*(2/V) ≤ 1) (hT : 0 ≤ T)
    (initial : MolecularState n) (i : Fin n) (m : PhysicalMark)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (hstop : ∀ l, MeasurableSet {h | stop l h}) :
    molecularLaw hn r d k V hr (fun i => (hd i).1) hk hV initial
      {z | ∃ l s, 0 ≤ s ∧
        s ≤ min (z (l+1)).2.2 (T-prefixElapsed l (Preorder.frestrictLe l z)) ∧
        δ+2/V ≤ |coordinateWithin (molecularRate r d k V)
          (markIncrement V i m) {N | materialSafe V N} T stop z l s|} ≤
      2*ENNReal.ofReal (Real.exp (-θ*δ+θ^2*(9/(4*V))*T)) := by
  apply coordinate_interval_tail initial (molecularNext r d k) (molecularRate r d k V)
    (markIncrement V i m)
    (molecular_rate_nonnegative r d k V hr (fun i => (hd i).1) hk hV.le)
    (molecular_total_positive hn r d k V hr (fun i => (hd i).1) hk hV)
    {N | materialSafe V N} θ (9/(4*V)) T (2/V) hθ (by positivity) hT (by positivity)
    (fun N a => markIncrement_bound V hV i m N a) _ _ stop hstop δ
  · intro N _ a
    rw [abs_mul,abs_of_nonneg hθ]
    exact (mul_le_mul_of_nonneg_left (markIncrement_bound V hV i m N a) hθ).trans hsmall
  · intro N hN
    exact marked_variance_bound r d k V hV (fun i => (hd i).2) N hN i m

end
end RAF1519.Refinement
