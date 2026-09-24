import proofs.FiniteCopy.MarkedUniformization

namespace FiniteCopy
open scoped NNReal

namespace MarkedKernel
variable {α β : Type*} [Fintype β] (P : MarkedKernel α β)

theorem law_add (f g : α → ℝ → ℝ) (k : ℕ) (x : α) (z : ℝ) :
    P.law k (fun y w => f y w+g y w) x z = P.law k f x z+P.law k g x z := by
  induction k generalizing x z with
  | zero => rfl
  | succ k ih => simp only [law,step,ih,mul_add,Finset.sum_add_distrib]

theorem event_union_le (A B : Set (α × ℝ)) (t : ℝ≥0) (x : α) (z : ℝ) :
    P.poissonized t (eventIndicator (A ∪ B)) x z ≤
      P.poissonized t (eventIndicator A) x z+P.poissonized t (eventIndicator B) x z := by
  classical
  have h (y : α) (w : ℝ) : eventIndicator (A ∪ B) y w ≤ eventIndicator A y w+eventIndicator B y w := by
    simp only [eventIndicator,Set.mem_union]
    split_ifs <;> simp_all
  have hk (k : ℕ) := P.law_mono _ _ h k x z
  simp only [P.law_add] at hk
  have hs := (P.event_summable t A x z).add (P.event_summable t B x z)
  have hh := Summable.tsum_le_tsum
    (fun k => mul_le_mul_of_nonneg_left (hk k) (poissonWeight_nonneg t k))
    (P.event_summable t (A ∪ B) x z) (by simpa only [mul_add] using hs)
  simpa only [mul_add,(P.event_summable t A x z).tsum_add (P.event_summable t B x z),poissonized] using hh

end MarkedKernel

namespace FiniteJumpModel
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (M : FiniteJumpModel α β)

theorem marked_step_marginal (mark : β → ℝ) (q : ℝ) (hq : 0 < q)
    (hc : ∀ x, M.total x ≤ q) (f : α → ℝ) (x : α) (z : ℝ) :
    (M.withMarks mark q hq hc).step (fun y _ => f y) x z = (M.uniformize q hq hc).step f x := by
  rw [M.uniformize_step]
  simp only [MarkedKernel.step,Fintype.sum_option,withMarks]
  simp only [generator,mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  unfold total
  ring

theorem marked_law_marginal (mark : β → ℝ) (q : ℝ) (hq : 0 < q)
    (hc : ∀ x, M.total x ≤ q) (f : α → ℝ) (k : ℕ) (x : α) (z : ℝ) :
    (M.withMarks mark q hq hc).law k (fun y _ => f y) x z = (M.uniformize q hq hc).steps k f x := by
  induction k generalizing x z with
  | zero => rfl
  | succ k ih =>
    change (M.withMarks mark q hq hc).step
      ((M.withMarks mark q hq hc).law k (fun y _ => f y)) x z = _
    rw [show (M.withMarks mark q hq hc).law k (fun y _ => f y) =
      (fun y _ => (M.uniformize q hq hc).steps k f y) from funext (fun y => funext (ih y))]
    exact M.marked_step_marginal mark q hq hc _ x z

theorem marked_poissonized_marginal (mark : β → ℝ) (q : ℝ) (hq : 0 < q)
    (hc : ∀ x, M.total x ≤ q) (A : Set α) (t : ℝ≥0) (x : α) (z : ℝ) :
    (M.withMarks mark q hq hc).poissonized t (MarkedKernel.eventIndicator {s | s.1 ∈ A}) x z =
      (M.uniformize q hq hc).poissonized t (FiniteKernel.eventIndicator A) x := by
  unfold MarkedKernel.poissonized FiniteKernel.poissonized
  apply tsum_congr
  intro k
  congr 1
  exact M.marked_law_marginal mark q hq hc (FiniteKernel.eventIndicator A) k x z

end FiniteJumpModel
end FiniteCopy
