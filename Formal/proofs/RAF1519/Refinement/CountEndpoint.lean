import proofs.RAF1519.Refinement.CountPrimitive
import proofs.RAF1519.Refinement.HoldingEndpoint

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators
set_option maxHeartbeats 20000

/-- The new state at the exit jump is included. No goodness hypothesis is made
    on index j itself; only its preceding holding intervals must be unstopped. -/
theorem count_endpoint_primitive {n : ℕ} (r d : Fin n → ℝ)
    (k : Fin n → Fin n → ℝ) (V T : ℝ) (p : Fin n × Fin 7)
    (good : Set (MolecularState n))
    (stop : (l : ℕ) → (Finset.Iic l → JumpState (MolecularState n) (CountChannel n)) → Prop)
    (z : ℕ → JumpState (MolecularState n) (CountChannel n)) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K j : ℕ) (hj : j ≤ K) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ T)
    (hc : ∀ i < j, jumpConsistent (molecularNext r d k) (z i).1 (z (i+1)))
    (hs : ∀ i < j, ¬coordinateStop good T stop i (Preorder.frestrictLe i z)) :
    ((z j).1 p:ℝ)/V-coordinatePrefix (molecularRate r d k V) (molecularIncrement r d k V p)
      good T stop z j = countDriftPrimitive r d k V z K p (prefixElapsed j (Preorder.frestrictLe j z)) := by
  have hbefore : ∀ i < j, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh (Nat.succ_le_of_lt hi)
    rw [holdingClock_succ] at hm
    change prefixElapsed i (Preorder.frestrictLe i z)+(z (i+1)).2.2 ≤
      prefixElapsed j (Preorder.frestrictLe j z) at hm
    linarith
  rw [molecular_complete_prefix_identity r d k V T p good stop z j hc hs hbefore]
  rw [countDriftPrimitive,prefix_elapsed_holdingClock,holdingPrimitive_at_clock _ _ hh K j hj]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ a, molecularRate r d k V (z i).1 a*molecularIncrement r d k V p (z i).1 a)*
      (z (i+1)).2.2) j]
  ring

end
end RAF1519.Refinement
