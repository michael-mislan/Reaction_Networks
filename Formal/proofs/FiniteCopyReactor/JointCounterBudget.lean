import proofs.FiniteCopyReactor.JointSupplyTails
import proofs.FiniteCopyReactor.ThreeStageExpectations
import proofs.FiniteCopyReactor.RoundedService

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem joint_cycle_event_union (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (A B : Set (BoxCounts V × ReactorCounters)) (N : BoxCounts V) (z : ReactorCounters) :
    jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator (A ∪ B)) N z ≤
      jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator A) N z+
      jointCycle V r d hV hr hr' hd hd' (FiniteKernel.eventIndicator B) N z := by
  have h := three_stage_event_union (jointCycleKernel false false V r d hV hr hr' hd hd')
    (jointCycleKernel true false V r d hV hr hr' hd hd')
    (jointCycleKernel true true V r d hV hr hr' hd hd')
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    {s | s.1 ∈ A} {s | s.1 ∈ B} (N,z) 0
  convert h using 1

def FreeCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) :=
  {X | residenceActive V X.1 ∧ X.2 0 ≤ (V:ℝ)/1080+1}
def TemplateCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) :=
  {X | residenceActive V X.1 ∧ X.2 1 ≤ (V:ℝ)/56+1}
def FoodUCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) := {X | 5*(V:ℝ) ≤ X.2 2}
def FoodWCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) := {X | 5*(V:ℝ) ≤ X.2 3}
def GrossCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) := {X | (V:ℝ)/5-1 ≤ X.2 4}

def JointCounterFailure (V : ℕ) : Set (BoxCounts V × ReactorCounters) :=
  (FreeCounterFailure V ∪ TemplateCounterFailure V) ∪
    ((FoodUCounterFailure V ∪ FoodWCounterFailure V) ∪ GrossCounterFailure V)

def jointCounterError (V : ℝ) : ℝ :=
  freeCollectionError V+Real.exp (-V/100000)+2*Real.exp (-V/300)+Real.exp (-V/2000)

theorem joint_counter_budget (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (N : BoxCounts V) (doseU doseW : ℝ)
    (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator (JointCounterFailure V)) N (initialCounters doseU doseW) ≤ jointCounterError V := by
  let C := fun A => jointCycle V r d hV (by linarith) hr' hd hd' (FiniteKernel.eventIndicator A) N (initialCounters doseU doseW)
  have h0 : C (FreeCounterFailure V) ≤ freeCollectionError V := by
    convert joint_free_tail V r d hV hlarge hr hr' hd hd' N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator FreeCounterFailure
    split_ifs <;> simp_all
  have h1 : C (TemplateCounterFailure V) ≤ Real.exp (-(V:ℝ)/100000) := by
    convert joint_template_tail V r d hV hlarge hr hr' hd hd' N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator TemplateCounterFailure
    split_ifs <;> simp_all
  have h2 : C (FoodUCounterFailure V) ≤ Real.exp (-(V:ℝ)/300) := joint_foodU_tail V r d hV (by linarith) hr' hd hd' N doseU doseW hu
  have h3 : C (FoodWCounterFailure V) ≤ Real.exp (-(V:ℝ)/300) := joint_foodW_tail V r d hV (by linarith) hr' hd hd' N doseU doseW hw
  have h4 : C (GrossCounterFailure V) ≤ Real.exp (-(V:ℝ)/2000) := joint_rounded_gross_tail V r d hV hlarge (by linarith) hr' hd hd' N doseU doseW
  have hU (A B) : C (A ∪ B) ≤ C A+C B := joint_cycle_event_union V r d hV (by linarith) hr' hd hd' A B N (initialCounters doseU doseW)
  have h01 := hU (FreeCounterFailure V) (TemplateCounterFailure V)
  have h23 := hU (FoodUCounterFailure V) (FoodWCounterFailure V)
  have h234 := hU (FoodUCounterFailure V ∪ FoodWCounterFailure V) (GrossCounterFailure V)
  have hall := hU (FreeCounterFailure V ∪ TemplateCounterFailure V)
    ((FoodUCounterFailure V ∪ FoodWCounterFailure V) ∪ GrossCounterFailure V)
  change C _ ≤ _
  unfold JointCounterFailure jointCounterError
  linarith

end
end FiniteCopyReactor
