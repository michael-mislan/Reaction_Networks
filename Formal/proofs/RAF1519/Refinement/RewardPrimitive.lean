import proofs.RAF1519.Refinement.CountPrimitive

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory RandomViability
open scoped BigOperators

variable {α β : Type*} [Fintype β]

/-- Sum the labels of the first K actual jumps; the initial dummy label is excluded. -/
def rewardPrefix (inc : α → β → ℝ) (z : ℕ → JumpState α β) (K : ℕ) : ℝ :=
  ∑ i : Fin K, (z ((i:ℕ)+1)).2.1.elim (fun _ => 0) (inc (z i).1)

theorem reward_complete_prefix_identity (rate inc : α → β → ℝ)
    (good : Set α) (T : ℝ)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (K : ℕ)
    (hs : ∀ i < K, ¬coordinateStop good T stop i (Preorder.frestrictLe i z))
    (ht : ∀ i < K, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z)) :
    coordinatePrefix rate inc good T stop z K = rewardPrefix inc z K-
      ∑ i : Fin K, (∑ a, rate (z i).1 a*inc (z i).1 a)*(z ((i:ℕ)+1)).2.2 := by
  unfold coordinatePrefix rewardPrefix
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold coordinateCompensation
  dsimp only
  rw [if_neg (hs i i.isLt),if_pos (ht i i.isLt),min_eq_left (ht i i.isLt)]
  rfl

theorem reward_minus_compensation_primitive (rate inc : α → β → ℝ)
    (good : Set α) (T : ℝ)
    (stop : (l : ℕ) → (Finset.Iic l → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (hh : ∀ i, 0 ≤ (z (i+1)).2.2)
    (K j : ℕ) (hj : j < K) (t : ℝ) (hT : t ≤ T)
    (ha : prefixElapsed j (Preorder.frestrictLe j z) ≤ t)
    (hb : t < prefixElapsed j (Preorder.frestrictLe j z)+(z (j+1)).2.2)
    (hs : ∀ i ≤ j, ¬coordinateStop good T stop i (Preorder.frestrictLe i z)) :
    rewardPrefix inc z j-coordinateWithin rate inc good T stop z j
      (t-prefixElapsed j (Preorder.frestrictLe j z)) =
      holdingPrimitive (fun i => (z (i+1)).2.2)
        (fun i => ∑ a, rate (z i).1 a*inc (z i).1 a) K t := by
  have hbefore : ∀ i < j, (z (i+1)).2.2 ≤ T-prefixElapsed i (Preorder.frestrictLe i z) := by
    intro i hi
    have hm := holdingClock_monotone (fun i => (z (i+1)).2.2) hh (Nat.succ_le_of_lt hi)
    rw [holdingClock_succ] at hm
    change prefixElapsed i (Preorder.frestrictLe i z)+(z (i+1)).2.2 ≤
      prefixElapsed j (Preorder.frestrictLe j z) at hm
    linarith
  rw [coordinateWithin,if_neg (hs j le_rfl),
    reward_complete_prefix_identity rate inc good T stop z j (fun i hi => hs i hi.le) hbefore]
  rw [holdingPrimitive_on_interval _ _ hh K j hj t ha hb]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    (∑ a, rate (z i).1 a*inc (z i).1 a)*(z (i+1)).2.2) j]
  simp only [prefix_elapsed_holdingClock]
  ring

end
end RAF1519.Refinement
