import proofs.RAF1519.Refinement.CensoredCoordinate

namespace RAF1519.Refinement
noncomputable section
open RandomViability
open scoped BigOperators
variable {α β : Type*}

theorem coordinate_elapsed_succ (z : ℕ → JumpState α β) (k : ℕ) :
    prefixElapsed (k+1) (Preorder.frestrictLe (k+1) z) =
      prefixElapsed k (Preorder.frestrictLe k z)+(z (k+1)).2.2 := by
  unfold prefixElapsed
  rw [Fin.sum_univ_castSucc]
  rfl

theorem coordinate_wait_le_increment (good : Set α) (T : ℝ)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (k : ℕ) (h : Finset.Iic k → JumpState α β) (y : JumpState α β) (hy : 0 ≤ y.2.2) :
    coordinateWait good T stop k h y ≤
      min T (prefixElapsed k h+y.2.2)-min T (prefixElapsed k h) := by
  by_cases hs : coordinateStop good T stop k h
  · rw [coordinateWait,if_pos hs]
    exact sub_nonneg.mpr (min_le_min_left T (le_add_of_nonneg_right hy))
  · have ht : prefixElapsed k h ≤ T := le_of_not_ge (not_or.mp (not_or.mp hs).2).2
    rw [coordinateWait,if_neg hs,min_eq_right ht]
    by_cases hn : T ≤ prefixElapsed k h+y.2.2
    · rw [min_eq_left hn]
      exact min_le_right _ _
    · rw [min_eq_right (le_of_not_ge hn)]
      have hh := min_le_left y.2.2 (T-prefixElapsed k h)
      linarith

theorem coordinate_time_bound (good : Set α) (T : ℝ) (hT : 0 ≤ T)
    (stop : (k : ℕ) → (Finset.Iic k → JumpState α β) → Prop)
    (z : ℕ → JumpState α β) (hz : ∀ i,0 ≤ (z (i+1)).2.2) (K : ℕ) :
    (∑ i : Fin K,coordinateWait good T stop
      i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1))) ≤ T := by
  have hh : ∀ K,(∑ i : Fin K,coordinateWait good T stop
      i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1))) ≤
      min T (prefixElapsed K (Preorder.frestrictLe K z)) := by
    intro K
    induction K with
    | zero => simp [prefixElapsed,min_eq_right hT]
    | succ K ih =>
      rw [Fin.sum_univ_castSucc,coordinate_elapsed_succ]
      have hc := coordinate_wait_le_increment good T stop K
        (Preorder.frestrictLe K z) (z (K+1)) (hz K)
      change (∑ i : Fin K,coordinateWait good T stop
        i (Preorder.frestrictLe (i:ℕ) z) (z ((i:ℕ)+1)))+
        coordinateWait good T stop K (Preorder.frestrictLe K z) (z (K+1)) ≤ _
      linarith
  exact (hh K).trans (min_le_left _ _)

end
end RAF1519.Refinement
