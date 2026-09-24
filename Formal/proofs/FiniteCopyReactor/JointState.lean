import proofs.FiniteCopyReactor.JointOutputMarginal

namespace FiniteCopyReactor
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy Classical
open scoped NNReal

theorem marked_general_marginal {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] (M : FiniteJumpModel α β)
    (mark : β → ℝ) (q : ℝ) (hq : 0 < q) (hc : ∀ x, M.total x ≤ q)
    (f : α → ℝ) (t : NNReal) (x : α) (z : ℝ) :
    (M.withMarks mark q hq hc).poissonized t (fun y _ => f y) x z=
      (M.uniformize q hq hc).poissonized t f x := by
  unfold MarkedKernel.poissonized FiniteKernel.poissonized
  apply tsum_congr
  intro n
  rw [M.marked_law_marginal]

def switchedState (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ) (N : BoxCounts V) : ℝ :=
  (materialKernel V r d hV hr hr' hd hd').poissonized ((8250:ℝ≥0)*V)
    (fun X => (residenceKernel V r d hV hr hr' hd hd').poissonized ((750:ℝ≥0)*V)
      (fun Y => (residenceKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V) f Y) X) N

theorem joint_state_marginal (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V → ℝ) (N : BoxCounts V) (doseU doseW : ℝ) :
    jointCycle V r d hV hr hr' hd hd' (fun X => f X.1) N (initialCounters doseU doseW)=
      switchedState V r d hV hr hr' hd hd' f N := by
  have h := joint_output_marginal false V r d hV hr hr' hd hd' (fun X _ => f X) N doseU doseW
  have hm (Y : BoxCounts V) :
      (outputScalar true true false V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V) (fun X _ => f X) Y 0=
      (residenceKernel V r d hV hr hr' hd hd').poissonized ((3000:ℝ≥0)*V) f Y := by
    simpa [outputScalar,outputMark,supplyModel,residenceKernel] using
      (marked_general_marginal (residenceModel V r d hV hr hd) freeWashoutMark
        (3000*(V:ℝ)) (by positivity) (residence_total_bound V r d hV hr hr' hd hd') f ((3000:ℝ≥0)*V) Y 0)
  simp_rw [hm] at h
  exact h

end
end FiniteCopyReactor
