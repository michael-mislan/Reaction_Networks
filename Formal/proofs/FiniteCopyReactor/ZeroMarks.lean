import proofs.FiniteCopyReactor.MarkedUpper

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

theorem zero_mark_law {α β : Type*} [Fintype α] [Fintype β]
    (P : MarkedKernel α β) (Q : FiniteKernel α) (hm : ∀ j, P.mark j=0)
    (hPQ : ∀ f x z, P.step (fun y _ => f y) x z=Q.step f x)
    (f : α → ℝ → ℝ) (n : ℕ) (x : α) (z : ℝ) :
    P.law n f x z=Q.steps n (fun y => f y z) x := by
  induction n generalizing x z with
  | zero => rfl
  | succ n ih =>
    change (∑ j,P.prob x j*P.law n f (P.next x j) (z+P.mark j)) = _
    simp only [hm,add_zero,ih]
    exact hPQ (Q.steps n (fun y => f y z)) x z

theorem zero_mark_poisson {α β : Type*} [Fintype α] [Fintype β]
    (P : MarkedKernel α β) (Q : FiniteKernel α) (hm : ∀ j, P.mark j=0)
    (hPQ : ∀ f x z, P.step (fun y _ => f y) x z=Q.step f x)
    (f : α → ℝ → ℝ) (t : NNReal) (x : α) (z : ℝ) :
    P.poissonized t f x z=Q.poissonized t (fun y => f y z) x := by
  unfold MarkedKernel.poissonized FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [zero_mark_law P Q hm hPQ]

end
end FiniteCopyReactor
