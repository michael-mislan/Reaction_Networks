import proofs.CompositionalMemory.JumpDeadline

namespace CompositionalMemory
open Classical RandomViability MeasureTheory ProbabilityTheory
open scoped ENNReal
noncomputable section
variable {α β : Type*}

theorem restart_population (z : ℕ → JumpState α β) (i : ℕ) :
    (restartJump z i).1 = (z (i+1)).1 := by cases i <;> rfl

theorem safeDeadlineIndex_succ (D : Set α) (T : ℝ) (z : ℕ → JumpState α β) (K : ℕ) :
    safeDeadlineIndex D T z (K+1) ↔
      (z 0).1 ∈ D ∧ 0 ≤ T ∧ safeDeadlineIndex D (T-(z 1).2.2) (restartJump z) K := by
  have he (i : ℕ) : jumpElapsed z (i+1) = (z 1).2.2+jumpElapsed (restartJump z) i :=
    restart_wait_sum z i
  constructor
  · intro h
    have h0 := h.1 0 (by omega)
    refine ⟨h0.1,?_,?_,?_⟩
    · simpa [jumpElapsed] using h0.2
    · intro i hi
      have hh := h.1 (i+1) (by omega)
      rw [restart_population]
      refine ⟨hh.1,?_⟩
      rw [he i] at hh
      linarith only [hh.2]
    · have hh := h.2
      rw [he (K+1)] at hh
      linarith only [hh]
  · rintro ⟨hD,hT,h⟩
    constructor
    · intro i hi
      cases i with
      | zero => exact ⟨hD,by simpa [jumpElapsed] using hT⟩
      | succ i =>
        have hh := h.1 i (by omega)
        rw [restart_population] at hh
        refine ⟨hh.1,?_⟩
        rw [he i]
        linarith only [hh.2]
    · rw [he (K+1)]
      linarith only [h.2]

theorem safeDeadlinePayoff_outside (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) (h : ¬((z 0).1 ∈ D ∧ 0 ≤ T)) :
    safeDeadlinePayoff D f T z=0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro K
  apply if_neg
  intro hK
  have hh := hK.1 0 (Nat.zero_le K)
  exact h ⟨hh.1,by simpa [jumpElapsed] using hh.2⟩

/-- Exact pathwise first-jump decomposition, including permanent unsafe-history loss. -/
theorem safeDeadlinePayoff_split (D : Set α) (f : α → ℝ≥0∞) (T : ℝ)
    (z : ℕ → JumpState α β) :
    safeDeadlinePayoff D f T z =
      if (z 0).1 ∈ D ∧ 0 ≤ T then
        (if T < (z 1).2.2 then f (z 0).1 else 0) +
          safeDeadlinePayoff D f (T-(z 1).2.2) (restartJump z)
      else 0 := by
  by_cases h : (z 0).1 ∈ D ∧ 0 ≤ T
  · rw [if_pos h]
    unfold safeDeadlinePayoff
    rw [tsum_eq_zero_add' ENNReal.summable]
    congr 1
    · have he : safeDeadlineIndex D T z 0 ↔ T < (z 1).2.2 := by
        simp [safeDeadlineIndex,jumpElapsed,h.1,h.2]
      rw [he]
    · apply tsum_congr
      intro K
      rw [safeDeadlineIndex_succ]
      simp only [h.1,h.2,true_and,restart_population]
  · rw [if_neg h]
    exact safeDeadlinePayoff_outside D f T z h

end
end CompositionalMemory
