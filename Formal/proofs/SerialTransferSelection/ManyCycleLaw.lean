import proofs.SerialTransferSelection.TwoCycle

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

/-- Full finite histories. Failed states, including `none`, are sampled normally. -/
noncomputable def finiteHistoryLaw {α : Type*} [Fintype α]
    (P : ℕ → α → FiniteLaw α) : (k : ℕ) → ℕ → α → FiniteLaw (Fin k → α)
  | 0, _, _ => FiniteLaw.pure Fin.elim0
  | k+1, j, x => (P j x).bind fun y =>
      (finiteHistoryLaw P k (j+1) y).bind fun h => FiniteLaw.pure (Fin.cons y h)

def historyGood {α : Type*} (R : ℕ → α → α → Prop) :
    (k : ℕ) → ℕ → α → (Fin k → α) → Prop
  | 0, _, _, _ => True
  | k+1, j, x, h => R j x (h 0) ∧ historyGood R k (j+1) (h 0) (Fin.tail h)

def historyBudget (d : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 0
  | k+1, j => d j + historyBudget d k (j+1)

theorem historyBudget_nonneg (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j) (k j : ℕ) :
    0 ≤ historyBudget d k j := by
  induction k generalizing j with
  | zero => exact le_rfl
  | succ k ih => exact add_nonneg (hd j) (ih (j+1))

/-- Conditional induction with stage-dependent errors, without independence. -/
theorem finiteHistoryLaw_probability {α : Type*} [Fintype α]
    (P : ℕ → α → FiniteLaw α) (R : ℕ → α → α → Prop)
    (I : ℕ → α → Prop) (d : ℕ → ℝ) (hd : ∀ j, 0 ≤ d j)
    (hstep : ∀ j x, I j x →
      1-d j ≤ (P j x).expect (FiniteKernel.eventIndicator {y | R j x y}))
    (hnext : ∀ j x y, I j x → R j x y → I (j+1) y)
    (k j : ℕ) (x : α) (hx : I j x) :
    1-historyBudget d k j ≤ (finiteHistoryLaw P k j x).expect
      (FiniteKernel.eventIndicator {h | historyGood R k j x h}) := by
  classical
  induction k generalizing j x with
  | zero => simp [finiteHistoryLaw, historyBudget, FiniteLaw.expect_pure,
      FiniteKernel.eventIndicator, historyGood]
  | succ k ih =>
    change 1-(d j+historyBudget d k (j+1)) ≤ _
    apply finiteLaw_joint_bind_lower _ _ {y | R j x y} _ _ _
      (historyBudget_nonneg d hd k (j+1)) (hstep j x hx)
    intro y hy
    change R j x y at hy
    have ht := ih (j+1) y (hnext j x y hx hy)
    rw [FiniteLaw.expect_bind]
    simp_rw [FiniteLaw.expect_pure]
    have he : (fun h => FiniteKernel.eventIndicator
        {h | historyGood R (k+1) j x h} (Fin.cons y h)) =
        FiniteKernel.eventIndicator {h | historyGood R k (j+1) y h} := by
      funext h
      simp [FiniteKernel.eventIndicator, historyGood, hy]
    rw [he]
    exact ht

end SerialTransferSelection
