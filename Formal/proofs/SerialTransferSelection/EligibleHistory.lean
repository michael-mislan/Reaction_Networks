import proofs.SerialTransferSelection.ManyCycleLaw

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

/-- Inspect a full original history through the first successful crossing cycle.
The protocol does not inspect this predicate or physically stop at band exit. -/
def eligibleHistoryGood {α : Type*} (I : ℕ → α → Prop) (R : ℕ → α → α → Prop) :
    (k : ℕ) → ℕ → α → (Fin k → α) → Prop
  | 0, _, _, _ => True
  | k+1, j, x, h => I j x → R j x (h 0) ∧
      eligibleHistoryGood I R k (j+1) (h 0) (Fin.tail h)

/-- Uniform conditional bounds before band exit give an unconditional inspection
guarantee. It does not assert that all K cycles remain eligible. -/
theorem eligibleHistory_probability {α : Type*} [Fintype α]
    (P : ℕ → α → FiniteLaw α) (R : ℕ → α → α → Prop)
    (I : ℕ → α → Prop) (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j)
    (hstep : ∀ j x, I j x →
      1-d j ≤ (P j x).expect (FiniteKernel.eventIndicator {y | R j x y}))
    (k j : ℕ) (x : α) :
    1-historyBudget d k j ≤ (finiteHistoryLaw P k j x).expect
      (FiniteKernel.eventIndicator {h | eligibleHistoryGood I R k j x h}) := by
  classical
  induction k generalizing j x with
  | zero => simp [finiteHistoryLaw,historyBudget,FiniteLaw.expect_pure,
      FiniteKernel.eventIndicator,eligibleHistoryGood]
  | succ k ih =>
    by_cases hx : I j x
    · change 1-(d j+historyBudget d k (j+1)) ≤ _
      apply finiteLaw_joint_bind_lower _ _ {y | R j x y} _ _ _
        (historyBudget_nonneg d hd k (j+1)) (hstep j x hx)
      intro y hy
      change R j x y at hy
      rw [FiniteLaw.expect_bind]
      simp_rw [FiniteLaw.expect_pure]
      have he : (fun h => FiniteKernel.eventIndicator
          {h | eligibleHistoryGood I R (k+1) j x h} (Fin.cons y h)) =
          FiniteKernel.eventIndicator {h | eligibleHistoryGood I R k (j+1) y h} := by
        funext h
        simp [FiniteKernel.eventIndicator,eligibleHistoryGood,hx,hy]
      rw [he]
      exact ih (j+1) y
    · have he : FiniteKernel.eventIndicator {h | eligibleHistoryGood I R (k+1) j x h} =
          (fun _ => (1 : ℝ)) := by
        funext h
        simp [FiniteKernel.eventIndicator,eligibleHistoryGood,hx]
      rw [he,FiniteLaw.expect_const]
      linarith [historyBudget_nonneg d hd (k+1) j]

end SerialTransferSelection
