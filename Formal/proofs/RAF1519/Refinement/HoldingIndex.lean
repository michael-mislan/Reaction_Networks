import proofs.RAF1519.Refinement.HoldingClock

namespace RAF1519.Refinement
noncomputable section
open Classical

/-- The interval containing t, selecting after all zero-duration intervals at t.
    The default branch is irrelevant on nonexplosive nonnegative-time paths. -/
def holdingIndex (h : ℕ → ℝ) (t : ℝ) : ℕ :=
  if e : ∃ j, holdingClock h j ≤ t ∧ t < holdingClock h j+h j then Nat.find e else 0

theorem holdingIndex_spec (h : ℕ → ℝ) (t : ℝ)
    (he : ∃ j, holdingClock h j ≤ t ∧ t < holdingClock h j+h j) :
    holdingClock h (holdingIndex h t) ≤ t ∧
      t < holdingClock h (holdingIndex h t)+h (holdingIndex h t) := by
  simp only [holdingIndex,dif_pos he]
  exact Nat.find_spec he

theorem holdingIndex_eq (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) (t : ℝ) (j : ℕ)
    (ha : holdingClock h j ≤ t) (hb : t < holdingClock h j+h j) : holdingIndex h t=j := by
  have he := holdingIndex_spec h t ⟨j,ha,hb⟩
  by_contra hn
  rcases lt_or_gt_of_ne hn with hj|hj
  · have hm := holdingClock_monotone h hh (Nat.succ_le_of_lt hj)
    rw [holdingClock_succ] at hm
    linarith [he.2]
  · have hm := holdingClock_monotone h hh (Nat.succ_le_of_lt hj)
    rw [holdingClock_succ] at hm
    linarith [he.1]

theorem holdingIndex_before_prefix (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i)
    (K : ℕ) (t : ℝ) (ht : 0 ≤ t) (hK : t < holdingClock h K) :
    holdingIndex h t < K ∧ holdingClock h (holdingIndex h t) ≤ t ∧
      t < holdingClock h (holdingIndex h t)+h (holdingIndex h t) := by
  obtain ⟨j,hj,ha,hb⟩ := holdingClock_covers h K t ht hK
  rw [holdingIndex_eq h hh t j ha hb]
  exact ⟨hj,ha,hb⟩

end
end RAF1519.Refinement
