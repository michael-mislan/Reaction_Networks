import proofs.FiniteCopyReactor.ThreeClock
import proofs.FiniteReservoir.CountCycleEvent
import proofs.FiniteReservoir.SourceCycleTransfer

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

theorem integer_three_source (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : JointCounts M → ℝ≥0∞) (X : BoxState V M × IntegerCounters) :
    threeClock (integerCycleKernel false false V M p hV)
      (integerCycleKernel true false V M p hV)
      (integerCycleKernel true true V M p hV)
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => f (integerCountState Y)) X =
      sourceStoppedCycle V M p hV f (integerCountState X) :=
  three_clock_map _ _ _ _ _ _ integerCountState _
    (integer_cycle_source_clock false false V M p hV)
    (integer_cycle_source_clock true false V M p hV)
    (integer_cycle_source_clock true true V M p hV) _ _ _ f X

theorem integer_three_real (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ≥0∞) (X : BoxState V M × IntegerCounters) :
    threeClock (integerCycleKernel false false V M p hV)
      (integerCycleKernel true false V M p hV)
      (integerCycleKernel true true V M p hV)
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => f (realCounterState Y)) X =
    threeClock (jointCycleKernel false false V M p hV)
      (jointCycleKernel true false V M p hV)
      (jointCycleKernel true true V M p hV)
      (3000*(V:ℝ)) (11/4) (1/4) 1 f (realCounterState X) :=
  three_clock_map _ _ _ _ _ _ realCounterState _
    (fun g Y T => integer_cycle_real_clock false false V M p hV g Y _ T)
    (fun g Y T => integer_cycle_real_clock true false V M p hV g Y _ T)
    (fun g Y T => integer_cycle_real_clock true true V M p hV g Y _ T) _ _ _ f X

end
end FiniteReservoir
