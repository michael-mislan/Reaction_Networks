import proofs.FiniteCopyReactor.JointCycle

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy

abbrev IntegerCounters := Fin 5 → ℕ

def integerCycleMarks (collect : Bool) (j : CompetitionChannel) : IntegerCounters :=
  fun i => Nat.floor (cycleMarks collect j i)

theorem integer_cycle_marks_exact (collect : Bool) (j : CompetitionChannel) (i : Fin 5) :
    (integerCycleMarks collect j i:ℝ)=cycleMarks collect j i := by
  cases collect <;> cases j with
  | inl j => fin_cases j <;> fin_cases i <;>
      norm_num [integerCycleMarks,cycleMarks,freeWashoutMark,templateMark,supplyMark,Fin.ext_iff]
  | inr j => fin_cases j <;> fin_cases i <;>
      norm_num [integerCycleMarks,cycleMarks,freeWashoutMark,templateMark,supplyMark,Fin.ext_iff]

def integerOptionMarks (collect : Bool) : Option CompetitionChannel → IntegerCounters
  | none => fun _ => 0
  | some j => integerCycleMarks collect j

theorem integer_option_marks_exact (collect : Bool) (j : Option CompetitionChannel) (i : Fin 5) :
    (integerOptionMarks collect j i:ℝ)=cycleOptionMarks collect j i := by
  cases j with
  | none => simp [integerOptionMarks,cycleOptionMarks]
  | some j => exact integer_cycle_marks_exact collect j i

def integerJointKernel {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → IntegerCounters) : MarkedKernel (α × IntegerCounters) β where
  prob X j := P.prob X.1 j
  next X j := (P.next X.1 j,fun i => X.2 i+marks j i)
  mark _ := 0
  nonneg X j := P.nonneg X.1 j
  row_sum X := P.row_sum X.1

def realCounterState {α : Type*} (X : α × IntegerCounters) : α × ReactorCounters :=
  (X.1,fun i => (X.2 i:ℝ))

theorem integer_joint_embedding {α β : Type*} [Fintype β] (P : MarkedKernel α β)
    (marks : β → IntegerCounters) (X : α × IntegerCounters) (j : β) :
    realCounterState ((integerJointKernel P marks).next X j)=
      (jointMarks P (fun b i => (marks b i:ℝ))).next (realCounterState X) j := by
  apply Prod.ext
  · rfl
  · funext i
    exact Nat.cast_add _ _

def integerCycleKernel (stopStock collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  integerJointKernel (supplyKernel stopStock .foodU V r d hV hr hr' hd hd') (integerOptionMarks collect)

theorem integer_cycle_embedding (b collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × IntegerCounters) (j : Option CompetitionChannel) :
    realCounterState ((integerCycleKernel b collect V r d hV hr hr' hd hd').next X j)=
      (jointCycleKernel b collect V r d hV hr hr' hd hd').next (realCounterState X) j := by
  apply Prod.ext
  · rfl
  · funext i
    change ((X.2 i+integerOptionMarks collect j i:ℕ):ℝ)=(X.2 i:ℝ)+cycleOptionMarks collect j i
    rw [Nat.cast_add,integer_option_marks_exact]

def integerInitialCounters (doseU doseW : ℕ) : IntegerCounters := ![0,0,doseU,doseW,0]

theorem integer_initial_counters_exact (doseU doseW : ℕ) :
    (fun i => (integerInitialCounters doseU doseW i:ℝ))=initialCounters doseU doseW := by
  funext i
  fin_cases i <;> norm_num [integerInitialCounters,initialCounters]

end
end FiniteCopyReactor
