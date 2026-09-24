import proofs.FiniteReservoir.JointSupplyTails
import proofs.FiniteCopyReactor.ThreeStageExpectations
import proofs.FiniteReservoir.RoundedService

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

theorem joint_cycle_event_union (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (A B : Set (BoxState V M × ReactorCounters)) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M p hV (FiniteKernel.eventIndicator (A ∪ B)) N z ≤
      jointCycle V M p hV (FiniteKernel.eventIndicator A) N z+
      jointCycle V M p hV (FiniteKernel.eventIndicator B) N z := by
  have h := three_stage_event_union (jointCycleKernel false false V M p hV)
    (jointCycleKernel true false V M p hV)
    (jointCycleKernel true true V M p hV)
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V)
    {s | s.1 ∈ A} {s | s.1 ∈ B} (N,z) 0
  convert h using 1

def FreeCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  {X | residenceActive V X.1.1 ∧ X.2 0 ≤ (V:ℝ)/1080+1}
def TemplateCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  {X | residenceActive V X.1.1 ∧ X.2 1 ≤ (V:ℝ)/56+1}
def FoodUCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) := {X | 5*(V:ℝ) ≤ X.2 2}
def FoodWCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) := {X | 5*(V:ℝ) ≤ X.2 3}
def GrossCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) := {X | (V:ℝ)/5-1 ≤ X.2 4}

def JointCounterFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  (FreeCounterFailure V M ∪ TemplateCounterFailure V M) ∪
    ((FoodUCounterFailure V M ∪ FoodWCounterFailure V M) ∪ GrossCounterFailure V M)

def jointCounterError (V : ℝ) : ℝ :=
  freeCollectionError V+Real.exp (-V/100000)+2*Real.exp (-V/300)+Real.exp (-V/2000)

theorem joint_counter_budget (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    
    (N : BoxState V M) (doseU doseW : ℝ)
    (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (FiniteKernel.eventIndicator (JointCounterFailure V M)) N (initialCounters doseU doseW) ≤ jointCounterError V := by
  let C := fun A => jointCycle V M p hV (FiniteKernel.eventIndicator A) N (initialCounters doseU doseW)
  have h0 : C (FreeCounterFailure V M) ≤ freeCollectionError V := by
    convert joint_free_tail V M p hV hlarge N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator FreeCounterFailure
    split_ifs <;> simp_all
  have h1 : C (TemplateCounterFailure V M) ≤ Real.exp (-(V:ℝ)/100000) := by
    convert joint_template_tail V M p hV hlarge N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator TemplateCounterFailure
    split_ifs <;> simp_all
  have h2 : C (FoodUCounterFailure V M) ≤ Real.exp (-(V:ℝ)/300) := joint_foodU_tail V M p hV N doseU doseW hu
  have h3 : C (FoodWCounterFailure V M) ≤ Real.exp (-(V:ℝ)/300) := joint_foodW_tail V M p hV N doseU doseW hw
  have h4 : C (GrossCounterFailure V M) ≤ Real.exp (-(V:ℝ)/2000) := joint_rounded_gross_tail V M p hV hlarge N doseU doseW
  have hU (A B) : C (A ∪ B) ≤ C A+C B := joint_cycle_event_union V M p hV A B N (initialCounters doseU doseW)
  have h01 := hU (FreeCounterFailure V M) (TemplateCounterFailure V M)
  have h23 := hU (FoodUCounterFailure V M) (FoodWCounterFailure V M)
  have h234 := hU (FoodUCounterFailure V M ∪ FoodWCounterFailure V M) (GrossCounterFailure V M)
  have hall := hU (FreeCounterFailure V M ∪ TemplateCounterFailure V M)
    ((FoodUCounterFailure V M ∪ FoodWCounterFailure V M) ∪ GrossCounterFailure V M)
  change C _ ≤ _
  unfold JointCounterFailure jointCounterError
  linarith

end
end FiniteReservoir
