import proofs.RAF1519.Refinement.RewardPrimitive
import proofs.RAF1519.Refinement.HoldingEndpoint

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

variable {α β : Type*} [Fintype β]

/-- The deadline jump is included even though its following holding interval is stopped. -/
theorem reward_endpoint_primitive (rate inc : α → β → ℝ)
    (good : Set α) (T : ℝ)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K j : ℕ) (hj : j ≤ K) (hT : prefixElapsed j (Preorder.frestrictLe j z) ≤ T)
    (hs : ∀ i < j, ¬coordinateStop good T stop i (Preorder.frestrictLe i z)) :
    rewardPrefix inc z j-coordinatePrefix rate inc good T stop z j =
      holdingPrimitive (fun i => (z (i+1)).2.2)
        (fun i => ∑ a, rate (z i).1 a*inc (z i).1 a) K
          (prefixElapsed j (Preorder.frestrictLe j z)) := by
  have hbefore : ∀ i < j, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh (Nat.succ_le_of_lt hi)
    rw [holdingClock_succ] at hm
    change prefixElapsed i (Preorder.frestrictLe i z)+(z (i+1)).2.2 ≤
      prefixElapsed j (Preorder.frestrictLe j z) at hm
    linarith
  rw [reward_complete_prefix_identity rate inc good T stop z j hs hbefore]
  rw [prefix_elapsed_holdingClock,holdingPrimitive_at_clock _ _ hh K j hj]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ a, rate (z i).1 a*inc (z i).1 a)*(z (i+1)).2.2) j]
  ring

end
end RAF1519.Refinement
