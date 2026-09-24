import proofs.FiniteReservoir.JointCycle
import proofs.FiniteCopyReactor.ZeroMarks

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

def outputMark (template : Bool) := if template then templateMark else freeWashoutMark

def outputScalar (b collect template : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  (supplyModel b V M p hV).withMarks
    (fun j => if collect then outputMark template j else 0)
    (3000*(V:ℝ)) (by positivity) (supply_total_bound b V M p hV)

def supplyStateKernel (b : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  (supplyModel b V M p hV).uniformize (3000*(V:ℝ)) (by positivity)
    (supply_total_bound b V M p hV)

theorem output_coordinate (b collect template : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :
    scalarMarks (supplyKernel b .foodU V M p hV) (cycleOptionMarks collect)
      (if template then 1 else 0) = outputScalar b collect template V M p hV := by
  unfold scalarMarks supplyKernel outputScalar FiniteJumpModel.withMarks
  congr 1
  funext j
  cases j with
  | none => rfl
  | some j => cases template <;> rfl

theorem output_before_collection (b template : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ → ℝ) (t : NNReal) (N : BoxState V M) (z : ℝ) :
    (outputScalar b false template V M p hV).poissonized t f N z =
      (supplyStateKernel b V M p hV).poissonized t (fun X => f X z) N := by
  apply zero_mark_poisson
  · intro j
    cases j <;> rfl
  · exact (supplyModel b V M p hV).marked_step_marginal _ _ _ _

theorem joint_output_marginal (template : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ → ℝ) (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV (fun X => f X.1 (X.2 (if template then 1 else 0)))
      N (initialCounters doseU doseW) =
    (materialKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
      (fun X => (residenceKernel V M p hV).poissonized ((750:ℝ≥0)*V)
        (fun Y => (outputScalar true true template V M p hV).poissonized
          ((3000:ℝ≥0)*V) f Y 0) X) N := by
  unfold jointCycle jointCycleKernel
  rw [joint_three_stage_coordinate]
  simp only [output_coordinate]
  unfold threeStage
  simp_rw [output_before_collection]
  have hz : initialCounters doseU doseW (if template then 1 else 0)=0 := by cases template <;> rfl
  rw [hz]
  rfl

end
end FiniteReservoir
