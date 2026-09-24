import proofs.FiniteCopyReactor.IntegerMarks
import proofs.FiniteReservoir.JointCycle

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor

def integerCycleKernel (stopStock collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
     :=
  integerJointKernel (supplyKernel stopStock .foodU V M p hV) (integerOptionMarks collect)

theorem integer_cycle_embedding (b collect : Bool) (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × IntegerCounters) (j : Option CompetitionChannel) :
    realCounterState ((integerCycleKernel b collect V M p hV).next X j)=
      (jointCycleKernel b collect V M p hV).next (realCounterState X) j := by
  apply Prod.ext
  · rfl
  · funext i
    change ((X.2 i+integerOptionMarks collect j i:ℕ):ℝ)=(X.2 i:ℝ)+cycleOptionMarks collect j i
    rw [Nat.cast_add,integer_option_marks_exact]


end
end FiniteReservoir
