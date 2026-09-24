import proofs.FiniteCopyReactor.MarkedUpper

namespace FiniteCopyReactor
noncomputable section
open FiniteCopy Classical

/-- All five counters are retained in the state of one reaction tree. -/
abbrev ReactorCounters := Fin 5 → ℝ

def jointMarks {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → ReactorCounters) : MarkedKernel (α × ReactorCounters) β where
  prob X j := P.prob X.1 j
  next X j := (P.next X.1 j,fun i => X.2 i+marks j i)
  mark _ := 0
  nonneg X j := P.nonneg X.1 j
  row_sum X := P.row_sum X.1

def scalarMarks {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → ReactorCounters) (i : Fin 5) : MarkedKernel α β where
  prob := P.prob
  next := P.next
  mark j := marks j i
  nonneg := P.nonneg
  row_sum := P.row_sum

theorem joint_marks_law_coordinate {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → ReactorCounters) (i : Fin 5) (f : α → ℝ → ℝ)
    (n : ℕ) (X : α × ReactorCounters) (a : ℝ) :
    (jointMarks P marks).law n (fun Y _ => f Y.1 (Y.2 i)) X a =
      (scalarMarks P marks i).law n f X.1 (X.2 i) := by
  induction n generalizing X a with
  | zero => rfl
  | succ n ih =>
    change (∑ j,P.prob X.1 j*(jointMarks P marks).law n (fun Y _ => f Y.1 (Y.2 i))
      (P.next X.1 j,fun k => X.2 k+marks j k) (a+0)) = _
    simp only [ih,MarkedKernel.law,MarkedKernel.step,scalarMarks]

theorem joint_marks_poisson_coordinate {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → ReactorCounters) (i : Fin 5) (f : α → ℝ → ℝ)
    (t : NNReal) (X : α × ReactorCounters) (a : ℝ) :
    (jointMarks P marks).poissonized t (fun Y _ => f Y.1 (Y.2 i)) X a =
      (scalarMarks P marks i).poissonized t f X.1 (X.2 i) := by
  unfold MarkedKernel.poissonized
  apply tsum_congr
  intro n
  rw [joint_marks_law_coordinate]

end
end FiniteCopyReactor
