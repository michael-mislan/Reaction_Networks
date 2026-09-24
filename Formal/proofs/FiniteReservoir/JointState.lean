import proofs.FiniteCopyReactor.JointState
import proofs.FiniteReservoir.JointOutputMarginal

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped NNReal

def switchedState (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ) (N : BoxState V M) : ℝ :=
  (materialKernel V M p hV).poissonized ((8250:ℝ≥0)*V)
    (fun X => (residenceKernel V M p hV).poissonized ((750:ℝ≥0)*V)
      (fun Y => (residenceKernel V M p hV).poissonized ((3000:ℝ≥0)*V) f Y) X) N

theorem joint_state_marginal (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M → ℝ) (N : BoxState V M) (doseU doseW : ℝ) :
    jointCycle V M p hV (fun X => f X.1) N (initialCounters doseU doseW)=
      switchedState V M p hV f N := by
  have h := joint_output_marginal false V M p hV (fun X _ => f X) N doseU doseW
  have hm (Y : BoxState V M) :
      (outputScalar true true false V M p hV).poissonized ((3000:ℝ≥0)*V) (fun X _ => f X) Y 0=
      (residenceKernel V M p hV).poissonized ((3000:ℝ≥0)*V) f Y := by
    simpa [outputScalar,outputMark,supplyModel,residenceKernel] using
      (marked_general_marginal (residenceModel V M p hV) freeWashoutMark
        (3000*(V:ℝ)) (by positivity) (residence_total V M p hV) f ((3000:ℝ≥0)*V) Y 0)
  simp_rw [hm] at h
  exact h

end
end FiniteReservoir
