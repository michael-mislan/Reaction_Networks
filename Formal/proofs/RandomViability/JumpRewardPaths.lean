import proofs.RandomViability.RewardPaths
import proofs.FiniteCopy.FiniteJump

namespace RandomViability
open Classical FiniteCopy
noncomputable section
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]

/-- `none` is the uniformization self-loop; every actual channel retains its
own label even when several channels have the same next state. -/
def labeledUniformize (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x, M.total x ≤ q) : FiniteLabeledKernel α (Option β) where
  next x b := match b with | none => x | some b => M.next x b
  prob x b := match b with | none => 1-M.total x/q | some b => M.rate x b/q
  nonneg x b := by
    cases b with
    | none => exact sub_nonneg.mpr ((div_le_one hq).mpr (hbound x))
    | some b => exact div_nonneg (M.nonneg x b) hq.le
  row_sum x := by
    simp only [Fintype.sum_option, ← Finset.sum_div, FiniteJumpModel.total]
    ring

theorem labeledUniformize_compat (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x, M.total x ≤ q) (f : α → ℝ) (x : α) :
    (M.uniformize q hq hbound).step f x =
      ∑ b, (labeledUniformize M q hq hbound).prob x b *
        f ((labeledUniformize M q hq hbound).next x b) := by
  rw [M.uniformize_step]
  simp only [labeledUniformize, Fintype.sum_option]
  unfold FiniteJumpModel.generator FiniteJumpModel.total
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, div_mul_eq_mul_div, ← Finset.sum_div]
  ring

def liftChannelReward (g : α → β → ℝ) (x : α) : Option β → ℝ
  | none => 0
  | some b => g x b

omit [DecidableEq α] in
theorem labeledUniformize_reward (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x, M.total x ≤ q) (g : α → β → ℝ) (x : α) :
    (∑ b, (labeledUniformize M q hq hbound).prob x b * liftChannelReward g x b) =
      (∑ b, M.rate x b * g x b)/q := by
  simp [labeledUniformize, liftChannelReward, Fintype.sum_option, div_mul_eq_mul_div, Finset.sum_div]

theorem jump_pathExpectation_eq_kernel (M : FiniteJumpModel α β) (q : ℝ) (hq : 0 < q)
    (hbound : ∀ x, M.total x ≤ q) (g : α → β → ℝ) (n : ℕ) (x : α) :
    (labeledUniformize M q hq hbound).pathExpectation (liftChannelReward g) n x =
      kernelAccumulatedReward (M.uniformize q hq hbound)
        (fun y => (∑ b, M.rate y b * g y b)/q) n x := by
  have hh := FiniteLabeledKernel.pathExpectation_eq_kernel (labeledUniformize M q hq hbound)
    (M.uniformize q hq hbound) (labeledUniformize_compat M q hq hbound) (liftChannelReward g) n x
  have he := funext (labeledUniformize_reward M q hq hbound g)
  rw [he] at hh
  exact hh

end
end RandomViability

