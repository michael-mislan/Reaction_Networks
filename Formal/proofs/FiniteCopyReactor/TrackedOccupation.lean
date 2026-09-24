import proofs.FiniteCopyReactor.StateMarks

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

/-- Add an occupation counter to the state while retaining every original
reaction choice and its original output mark. -/
def trackedOccupation {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (b : α → ℝ) : MarkedKernel (α × ℝ) β where
  prob x j := P.prob x.1 j
  next x j := (P.next x.1 j,x.2+b x.1)
  mark := P.mark
  nonneg x j := P.nonneg x.1 j
  row_sum x := P.row_sum x.1

theorem tracked_free_marginal {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (b : α → ℝ) (f : α → ℝ → ℝ) (n : ℕ) (x : α) (u z : ℝ) :
    (trackedOccupation P b).law n (fun y w => f y.1 w) (x,u) z=P.law n f x z := by
  induction n generalizing x u z with
  | zero => rfl
  | succ n ih =>
    change (∑ j,P.prob x j*(trackedOccupation P b).law n (fun y w => f y.1 w)
      (P.next x j,u+b x) (z+P.mark j)) = ∑ j,P.prob x j*P.law n f (P.next x j) (z+P.mark j)
    simp only [ih]

theorem tracked_bad_marginal {α β : Type*} [Fintype α] [Fintype β] (P : MarkedKernel α β)
    (b : α → ℝ) (f : α → ℝ → ℝ) (n : ℕ) (x : α) (u z : ℝ) :
    (trackedOccupation P b).law n (fun y _ => f y.1 y.2) (x,u) z=
      (stateMarks P (fun y _ => b y)).law n f x u := by
  induction n generalizing x u z with
  | zero => rfl
  | succ n ih =>
    change (trackedOccupation P b).step _ (x,u) z=(stateMarks P (fun y _ => b y)).step _ x u
    rw [state_marks_step]
    change (∑ j,P.prob x j*(trackedOccupation P b).law n (fun y _ => f y.1 y.2)
      (P.next x j,u+b x) (z+P.mark j)) = _
    simp only [ih]

end
end FiniteCopyReactor
