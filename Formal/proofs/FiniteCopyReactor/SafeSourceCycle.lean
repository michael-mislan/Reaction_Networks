import proofs.FiniteCopyReactor.CycleClockBridge

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

theorem real_three_joint_cycle (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (f : BoxCounts V × ReactorCounters → ℝ) (hf : ∀ X,0 ≤ f X ∧ f X ≤ 1)
    (X : BoxCounts V × ReactorCounters) :
    threeClock (jointCycleKernel false false V r d hV hr hr' hd hd')
      (jointCycleKernel true false V r d hV hr hr' hd hd')
      (jointCycleKernel true true V r d hV hr hr' hd hd')
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => ENNReal.ofReal (f Y)) X =
      ENNReal.ofReal (jointCycle V r d hV hr hr' hd hd' f X.1 X.2) := by
  have ht : ((3000:NNReal)*V)*(11/4)=8250*V := by ring
  have hu : ((3000:NNReal)*V)*(1/4)=750*V := by ring
  have hh := three_clock_real_nn
    (jointCycleKernel false false V r d hV hr hr' hd hd')
    (jointCycleKernel true false V r d hV hr hr' hd hd')
    (jointCycleKernel true true V r d hV hr hr' hd hd')
    ((3000:NNReal)*V) (11/4) (1/4) 1 f hf X
  simpa only [ht,hu,mul_one,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat,
    NNReal.coe_div,NNReal.coe_one,jointCycle,Prod.mk.eta] using hh

theorem joint_safe_source_lower (V : ℕ) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 0 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25)
    (X : BoxCounts V × IntegerCounters) :
    ENNReal.ofReal (jointCycle V r d hV hr hr' hd hd'
      (FiniteKernel.eventIndicator (realSafeEvent V)) X.1 (realCounterState X).2) ≤
      jointSourceCycle V r d hV hr hd (countSafePayoff V) (integerCountState X) := by
  have hs := integer_three_source V r d hV hr hr' hd hd' (countSafePayoff V) X
  have hf : (fun Y : BoxCounts V × IntegerCounters => countSafePayoff V (integerCountState Y))=
      (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V) (realCounterState Y))) := by
    funext Y
    exact count_safe_payoff_real V Y
  rw [hf,integer_three_real V r d hV hr hr' hd hd'
    (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V) Y)) X] at hs
  rw [real_three_joint_cycle V r d hV hr hr' hd hd' _ (FiniteKernel.eventIndicator_bounds _)] at hs
  exact hs.le.trans (source_cycle_transfer V r d hV hr hr' hd hd' _ (count_safe_payoff_bound V)
    (count_safe_payoff_zero V) (integerCountState X))

end
end FiniteCopyReactor
