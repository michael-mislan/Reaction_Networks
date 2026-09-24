import proofs.FiniteCopyReactor.ThreeClock
import proofs.FiniteCopyReactor.CountCycleEvent
import proofs.FiniteCopyReactor.SourceCycleTransfer

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

theorem integer_three_source (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : JointCounts → ℝ≥0∞) (X : BoxCounts V × IntegerCounters) :
    threeClock (integerCycleKernel false false V r d hV hr hr' hd hd')
      (integerCycleKernel true false V r d hV hr hr' hd hd')
      (integerCycleKernel true true V r d hV hr hr' hd hd')
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => f (integerCountState Y)) X =
      sourceStoppedCycle V r d hV hr hr' hd hd' f (integerCountState X) :=
  three_clock_map _ _ _ _ _ _ integerCountState _
    (integer_cycle_source_clock false false V r d hV hr hr' hd hd')
    (integer_cycle_source_clock true false V r d hV hr hr' hd hd')
    (integer_cycle_source_clock true true V r d hV hr hr' hd hd') _ _ _ f X

theorem integer_three_real (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ≥0∞) (X : BoxCounts V × IntegerCounters) :
    threeClock (integerCycleKernel false false V r d hV hr hr' hd hd')
      (integerCycleKernel true false V r d hV hr hr' hd hd')
      (integerCycleKernel true true V r d hV hr hr' hd hd')
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => f (realCounterState Y)) X =
    threeClock (jointCycleKernel false false V r d hV hr hr' hd hd')
      (jointCycleKernel true false V r d hV hr hr' hd hd')
      (jointCycleKernel true true V r d hV hr hr' hd hd')
      (3000*(V:ℝ)) (11/4) (1/4) 1 f (realCounterState X) :=
  three_clock_map _ _ _ _ _ _ realCounterState _
    (fun g Y T => integer_cycle_real_clock false false V r d hV hr hr' hd hd' g Y _ T)
    (fun g Y T => integer_cycle_real_clock true false V r d hV hr hr' hd hd' g Y _ T)
    (fun g Y T => integer_cycle_real_clock true true V r d hV hr hr' hd hd' g Y _ T) _ _ _ f X

end
end FiniteCopyReactor
