import proofs.FiniteCopy.FiniteJump
import Mathlib.Tactic

namespace RandomViability
open Classical FiniteCopy
noncomputable section
set_option maxHeartbeats 20000

theorem three_model_clock_exists {α β σ γ τ δ : Type*}
    [Fintype α] [Fintype β] [Fintype σ] [Fintype γ] [Fintype τ] [Fintype δ]
    (M : FiniteJumpModel α β) (R : FiniteJumpModel σ γ) (L : FiniteJumpModel τ δ) :
    ∃ q : NNReal, 1 ≤ (q : ℝ) ∧ (∀ x, M.total x ≤ q) ∧
      (∀ x, R.total x ≤ q) ∧ (∀ x, L.total x ≤ q) := by
  have hM : ∀ x, 0 ≤ M.total x := fun x => Finset.sum_nonneg (fun b _ => M.nonneg x b)
  have hR : ∀ x, 0 ≤ R.total x := fun x => Finset.sum_nonneg (fun b _ => R.nonneg x b)
  have hL : ∀ x, 0 ≤ L.total x := fun x => Finset.sum_nonneg (fun b _ => L.nonneg x b)
  let m : ℝ := ∑ x, M.total x
  let r : ℝ := ∑ x, R.total x
  let l : ℝ := ∑ x, L.total x
  have hm : 0 ≤ m := Finset.sum_nonneg (fun x _ => hM x)
  have hr : 0 ≤ r := Finset.sum_nonneg (fun x _ => hR x)
  have hl : 0 ≤ l := Finset.sum_nonneg (fun x _ => hL x)
  refine ⟨⟨1+m+r+l, by positivity⟩, ?_, ?_, ?_, ?_⟩
  · change 1 ≤ 1+m+r+l
    linarith
  · intro x
    have hh : M.total x ≤ m := Finset.single_le_sum (fun y _ => hM y) (Finset.mem_univ x)
    change M.total x ≤ 1+m+r+l
    linarith
  · intro x
    have hh : R.total x ≤ r := Finset.single_le_sum (fun y _ => hR y) (Finset.mem_univ x)
    change R.total x ≤ 1+m+r+l
    linarith
  · intro x
    have hh : L.total x ≤ l := Finset.single_le_sum (fun y _ => hL y) (Finset.mem_univ x)
    change L.total x ≤ 1+m+r+l
    linarith

end
end RandomViability
