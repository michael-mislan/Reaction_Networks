import proofs.FiniteCopyReactor.JointMarks
import proofs.FiniteCopyReactor.SupplyBudget
import proofs.FiniteCopyReactor.TemplateThreshold
import proofs.FiniteCopyReactor.FreeThreshold

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

/-- Coordinates: free X, template equivalents, food U, food W, gross service.
Only the final one-unit segment admits output marks. -/
def cycleMarks (collect : Bool) (j : CompetitionChannel) : ReactorCounters :=
  ![if collect then freeWashoutMark j else 0,
    if collect then templateMark j else 0,
    supplyMark .foodU j,supplyMark .foodW j,supplyMark .gross j]

def cycleOptionMarks (collect : Bool) : Option CompetitionChannel → ReactorCounters
  | none => fun _ => 0
  | some j => cycleMarks collect j

def jointCycleKernel (stopStock collect : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  jointMarks (supplyKernel stopStock .foodU V r d hV hr hr' hd hd') (cycleOptionMarks collect)

def initialCounters (doseU doseW : ℝ) : ReactorCounters := ![0,0,doseU,doseW,0]

/-- The same chemical state and every accumulated counter pass each boundary.
The extra scalar mark is identically zero and has no physical meaning. -/
def jointCycle (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (N : BoxCounts V) (z : ReactorCounters) : ℝ :=
  threeStage (jointCycleKernel false false V r d hV hr hr' hd hd')
    (jointCycleKernel true false V r d hV hr hr' hd hd')
    (jointCycleKernel true true V r d hV hr hr' hd hd')
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) (fun X _ => f X) (N,z) 0

theorem joint_three_stage_coordinate {α β γ δ : Type*} [Fintype β] [Fintype γ] [Fintype δ]
    (P : MarkedKernel α β) (Q : MarkedKernel α γ) (R : MarkedKernel α δ)
    (p : β → ReactorCounters) (q : γ → ReactorCounters) (r : δ → ReactorCounters)
    (i : Fin 5) (t u v : NNReal) (f : α → ℝ → ℝ) (X : α × ReactorCounters) (a : ℝ) :
    threeStage (jointMarks P p) (jointMarks Q q) (jointMarks R r) t u v
      (fun Y _ => f Y.1 (Y.2 i)) X a =
    threeStage (scalarMarks P p i) (scalarMarks Q q i) (scalarMarks R r i) t u v f X.1 (X.2 i) := by
  unfold threeStage
  simp_rw [joint_marks_poisson_coordinate]

theorem supply_coordinate (b collect : Bool) (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    scalarMarks (supplyKernel b .foodU V r d hV hr hr' hd hd') (cycleOptionMarks collect)
      (match k with | .foodU => 2 | .foodW => 3 | .gross => 4) =
    supplyKernel b k V r d hV hr hr' hd hd' := by
  cases k <;> unfold scalarMarks supplyKernel FiniteJumpModel.withMarks
  all_goals
    congr 1
    funext j
    cases j <;> rfl

theorem joint_cycle_supply_marginal (k : SupplyKind) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ → ℝ) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd'
      (fun X => f X.1 (X.2 (match k with | .foodU => 2 | .foodW => 3 | .gross => 4))) N z =
    supplyCycle k V r d hV hr hr' hd hd' f N
      (z (match k with | .foodU => 2 | .foodW => 3 | .gross => 4)) := by
  unfold jointCycle jointCycleKernel
  rw [joint_three_stage_coordinate]
  simp only [supply_coordinate,supplyCycle]

end
end FiniteCopyReactor
