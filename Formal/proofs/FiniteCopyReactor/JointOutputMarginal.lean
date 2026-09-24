import proofs.FiniteCopyReactor.JointCycle
import proofs.FiniteCopyReactor.ZeroMarks

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

def outputMark (template : Bool) := if template then templateMark else freeWashoutMark

def outputScalar (b collect template : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  (supplyModel b V r d hV hr hd).withMarks
    (fun j => if collect then outputMark template j else 0)
    (3000*(V:ℝ)) (by positivity) (supply_total_bound b V r d hV hr hr' hd hd')

def supplyStateKernel (b : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :=
  (supplyModel b V r d hV hr hd).uniformize (3000*(V:ℝ)) (by positivity)
    (supply_total_bound b V r d hV hr hr' hd hd')

theorem output_coordinate (b collect template : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    scalarMarks (supplyKernel b .foodU V r d hV hr hr' hd hd') (cycleOptionMarks collect)
      (if template then 1 else 0) = outputScalar b collect template V r d hV hr hr' hd hd' := by
  unfold scalarMarks supplyKernel outputScalar FiniteJumpModel.withMarks
  congr 1
  funext j
  cases j with
  | none => rfl
  | some j => cases template <;> rfl

theorem output_before_collection (b template : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ → ℝ) (t : NNReal) (N : BoxCounts V) (z : ℝ) :
    (outputScalar b false template V r d hV hr hr' hd hd').poissonized t f N z =
      (supplyStateKernel b V r d hV hr hr' hd hd').poissonized t (fun X => f X z) N := by
  apply zero_mark_poisson
  · intro j
    cases j <;> rfl
  · exact (supplyModel b V r d hV hr hd).marked_step_marginal _ _ _ _

theorem joint_output_marginal (template : Bool) (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ → ℝ) (N : BoxCounts V) (doseU doseW : ℝ) :
    jointCycle V r d hV hr hr' hd hd' (fun X => f X.1 (X.2 (if template then 1 else 0)))
      N (initialCounters doseU doseW) =
    (materialKernel V r d hV hr hr' hd hd').poissonized ((8250:ℝ≥0)*V)
      (fun X => (residenceKernel V r d hV hr hr' hd hd').poissonized ((750:ℝ≥0)*V)
        (fun Y => (outputScalar true true template V r d hV hr hr' hd hd').poissonized
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
end FiniteCopyReactor
