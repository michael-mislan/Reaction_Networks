import proofs.SerialTransferSelection.TransferCentered

namespace SerialTransferSelection
open HeritableCompositions FiniteCopy

def successfulOutput {α : Type*} (R : α → Prop) : Set (Option α) :=
  {x | match x with | none => False | some y => R y}

/-- Analytical failure quotient: failed branches contribute none with their full
original mass. The guard does not condition or resample the physical source. -/
noncomputable def guardedPush {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (A : Set α) (f : ∀ x, x ∈ A → β) : FiniteLaw (Option β) := by
  classical
  exact μ.bind (fun x => if hx : x ∈ A then FiniteLaw.pure (some (f x hx)) else FiniteLaw.pure none)

theorem guardedPush_probability {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (A : Set α) (f : ∀ x, x ∈ A → β)
    (R : β → Prop) (hR : ∀ x hx, R (f x hx)) :
    (guardedPush μ A f).expect (FiniteKernel.eventIndicator (successfulOutput R)) =
      μ.expect (FiniteKernel.eventIndicator A) := by
  classical
  unfold guardedPush
  rw [FiniteLaw.expect_bind]
  apply congrArg μ.expect
  funext x
  by_cases hx : x ∈ A
  · simp [hx,FiniteLaw.expect_pure,FiniteKernel.eventIndicator,successfulOutput,hR]
  · simp [hx,FiniteLaw.expect_pure,FiniteKernel.eventIndicator,successfulOutput]

theorem finiteLaw_event_nonneg {α : Type*} [Fintype α] (μ : FiniteLaw α) (A : Set α) :
    0 ≤ μ.expect (FiniteKernel.eventIndicator A) := by
  classical
  have h := μ.expect_mono (fun _ => 0) (FiniteKernel.eventIndicator A)
    (by intro x; simp only [FiniteKernel.eventIndicator]; split_ifs <;> norm_num)
  simpa only [FiniteLaw.expect_const] using h

/-- Conditional composition on actual finite laws; no independence is required. -/
theorem finiteLaw_joint_bind_lower {α β : Type*} [Fintype α] [Fintype β]
    (μ : FiniteLaw α) (ν : α → FiniteLaw β) (A : Set α) (B : Set β)
    (e₁ e₂ : ℝ) (he₂ : 0 ≤ e₂)
    (hμ : 1-e₁ ≤ μ.expect (FiniteKernel.eventIndicator A))
    (hν : ∀ x ∈ A, 1-e₂ ≤ (ν x).expect (FiniteKernel.eventIndicator B)) :
    1-(e₁+e₂) ≤ (μ.bind ν).expect (FiniteKernel.eventIndicator B) := by
  classical
  rw [FiniteLaw.expect_bind]
  have h := μ.expect_mono (fun x => FiniteKernel.eventIndicator A x-e₂)
    (fun x => (ν x).expect (FiniteKernel.eventIndicator B)) (by
      intro x
      by_cases hx : x ∈ A
      · simpa only [FiniteKernel.eventIndicator,if_pos hx] using hν x hx
      · have hn := finiteLaw_event_nonneg (ν x) B
        simp only [FiniteKernel.eventIndicator,if_neg hx]
        linarith)
  rw [finiteLaw_expect_sub,FiniteLaw.expect_const] at h
  linarith only [h,hμ]

end SerialTransferSelection
