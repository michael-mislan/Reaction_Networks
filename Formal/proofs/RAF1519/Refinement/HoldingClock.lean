import proofs.RAF1519.Refinement.HoldingRamp

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators

def holdingClock (h : ℕ → ℝ) (k : ℕ) : ℝ := ∑ i : Fin k, h i

theorem holdingClock_zero (h : ℕ → ℝ) : holdingClock h 0 = 0 := by simp [holdingClock]

theorem holdingClock_succ (h : ℕ → ℝ) (k : ℕ) :
    holdingClock h (k+1) = holdingClock h k+h k := by
  unfold holdingClock
  rw [Fin.sum_univ_castSucc]
  rfl

theorem holdingClock_monotone (h : ℕ → ℝ) (hh : ∀ i, 0 ≤ h i) : Monotone (holdingClock h) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [holdingClock_succ]
  exact le_add_of_nonneg_right (hh k)

/-- A finite chronological prefix extending beyond t contains a holding interval
    covering t. Zero-length intervals do not cause an ambiguity in this witness. -/
theorem holdingClock_covers (h : ℕ → ℝ) (K : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hK : t < holdingClock h K) :
    ∃ j, j < K ∧ holdingClock h j ≤ t ∧ t < holdingClock h j+h j := by
  induction K with
  | zero => simp only [holdingClock_zero] at hK; linarith
  | succ K ih =>
    by_cases hk : t < holdingClock h K
    · obtain ⟨j,hj,ha,hb⟩ := ih hk
      exact ⟨j,Nat.lt_succ_of_lt hj,ha,hb⟩
    · exact ⟨K,Nat.lt_succ_self K,le_of_not_gt hk,by rwa [holdingClock_succ] at hK⟩

theorem holdingRamp_completed (a h t : ℝ) (hh : 0 ≤ h) (ht : a+h ≤ t) :
    holdingRamp a h t = h := by
  simp only [holdingRamp,min_eq_left (show h ≤ t-a by linarith),max_eq_right hh]

theorem holdingRamp_not_started (a h t : ℝ) (ht : t ≤ a) : holdingRamp a h t = 0 := by
  unfold holdingRamp
  exact max_eq_left ((min_le_right h (t-a)).trans (sub_nonpos.mpr ht))

theorem holdingRamp_current (a h t : ℝ) (ha : a ≤ t) (hb : t ≤ a+h) :
    holdingRamp a h t = t-a := by
  simp only [holdingRamp,min_eq_right (show t-a ≤ h by linarith),max_eq_right (sub_nonneg.mpr ha)]

end
end RAF1519.Refinement
