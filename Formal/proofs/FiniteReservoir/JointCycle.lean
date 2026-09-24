import proofs.FiniteCopyReactor.JointCycle
import proofs.FiniteReservoir.SupplyBudget
import proofs.FiniteReservoir.TemplateThreshold
import proofs.FiniteReservoir.FreeThreshold

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

def jointCycleKernel (stopStock collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  jointMarks (supplyKernel stopStock .foodU V M p hV) (cycleOptionMarks collect)

/-- The same chemical state and every accumulated counter pass each boundary.
The extra scalar mark is identically zero and has no physical meaning. -/
def jointCycle (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ) (N : BoxState V M) (z : ReactorCounters) : ℝ :=
  threeStage (jointCycleKernel false false V M p hV)
    (jointCycleKernel true false V M p hV)
    (jointCycleKernel true true V M p hV)
    ((8250:ℝ≥0)*V) ((750:ℝ≥0)*V) ((3000:ℝ≥0)*V) (fun X _ => f X) (N,z) 0

theorem supply_coordinate (b collect : Bool) (k : SupplyKind) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :
    scalarMarks (supplyKernel b .foodU V M p hV) (cycleOptionMarks collect)
      (match k with | .foodU => 2 | .foodW => 3 | .gross => 4) =
    supplyKernel b k V M p hV := by
  cases k <;> unfold scalarMarks supplyKernel FiniteJumpModel.withMarks
  all_goals
    congr 1
    funext j
    cases j <;> rfl

theorem joint_cycle_supply_marginal (k : SupplyKind) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ → ℝ) (N : BoxState V M) (z : ReactorCounters) :
    jointCycle V M p hV
      (fun X => f X.1 (X.2 (match k with | .foodU => 2 | .foodW => 3 | .gross => 4))) N z =
    supplyCycle k V M p hV f N
      (z (match k with | .foodU => 2 | .foodW => 3 | .gross => 4)) := by
  unfold jointCycle jointCycleKernel
  rw [joint_three_stage_coordinate]
  simp only [supply_coordinate,supplyCycle]

end
end FiniteReservoir
