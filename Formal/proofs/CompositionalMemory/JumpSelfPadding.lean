import proofs.FiniteCopy.FiniteJump

namespace CompositionalMemory
open Classical FiniteCopy
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β]

/-- A rate-one state-preserving event makes absorbing states legal exponential-jump states. -/
def selfPaddedModel (M : FiniteJumpModel α β) : FiniteJumpModel α (Unit ⊕ β) where
  next x b := b.elim (fun _ => x) (M.next x)
  rate x b := b.elim (fun _ => 1) (M.rate x)
  nonneg x b := by cases b with
    | inl u => exact zero_le_one
    | inr b => exact M.nonneg x b

theorem selfPadded_total (M : FiniteJumpModel α β) (x : α) :
    (selfPaddedModel M).total x=1+M.total x := by
  simp [FiniteJumpModel.total,selfPaddedModel,Fintype.sum_sum_type]

theorem selfPadded_total_positive (M : FiniteJumpModel α β) (x : α) :
    0 < ∑ b,(selfPaddedModel M).rate x b := by
  have h : 0 ≤ M.total x := Finset.sum_nonneg (fun b _ => M.nonneg x b)
  change 0 < (selfPaddedModel M).total x
  rw [selfPadded_total]
  linarith

theorem selfPadded_generator (M : FiniteJumpModel α β) (f : α → ℝ) (x : α) :
    (selfPaddedModel M).generator f x=M.generator f x := by
  simp [FiniteJumpModel.generator,selfPaddedModel,Fintype.sum_sum_type]

theorem finiteKernel_eq_of_prob {P Q : FiniteKernel α} (h : P.prob=Q.prob) : P=Q := by
  cases P
  cases Q
  cases h
  rfl

variable [DecidableEq α]

/-- Padding changes neither the state generator nor the common-clock transition kernel. -/
theorem selfPadded_uniformize (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hM : ∀ x,M.total x ≤ q) (hP : ∀ x,(selfPaddedModel M).total x ≤ q) :
    (selfPaddedModel M).uniformize q hq hP=M.uniformize q hq hM := by
  apply finiteKernel_eq_of_prob
  funext x y
  let f : α → ℝ := fun z => if z=y then 1 else 0
  have hs (P : FiniteKernel α) : P.step f x=P.prob x y := by
    simp [FiniteKernel.step,f]
  have he : ((selfPaddedModel M).uniformize q hq hP).step f x=
      (M.uniformize q hq hM).step f x := by
    rw [FiniteJumpModel.uniformize_step,FiniteJumpModel.uniformize_step,selfPadded_generator]
  rw [hs,hs] at he
  exact he

end
end CompositionalMemory
