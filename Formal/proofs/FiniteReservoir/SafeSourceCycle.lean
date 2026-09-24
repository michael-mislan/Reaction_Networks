import proofs.FiniteReservoir.CycleClockBridge

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

theorem real_three_joint_cycle (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (f : BoxState V M × ReactorCounters → ℝ) (hf : ∀ X,0 ≤ f X ∧ f X ≤ 1)
    (X : BoxState V M × ReactorCounters) :
    threeClock (jointCycleKernel false false V M p hV)
      (jointCycleKernel true false V M p hV)
      (jointCycleKernel true true V M p hV)
      (3000*(V:ℝ)) (11/4) (1/4) 1 (fun Y => ENNReal.ofReal (f Y)) X =
      ENNReal.ofReal (jointCycle V M p hV f X.1 X.2) := by
  have ht : ((3000:NNReal)*V)*(11/4)=8250*V := by ring
  have hu : ((3000:NNReal)*V)*(1/4)=750*V := by ring
  have hh := three_clock_real_nn
    (jointCycleKernel false false V M p hV)
    (jointCycleKernel true false V M p hV)
    (jointCycleKernel true true V M p hV)
    ((3000:NNReal)*V) (11/4) (1/4) 1 f hf X
  simpa only [ht,hu,mul_one,NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_ofNat,
    NNReal.coe_div,NNReal.coe_one,jointCycle,Prod.mk.eta] using hh

theorem joint_safe_source_lower (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    
    (X : BoxState V M × IntegerCounters) :
    ENNReal.ofReal (jointCycle V M p hV
      (FiniteKernel.eventIndicator (realSafeEvent V M)) X.1 (realCounterState X).2) ≤
      jointSourceCycle V M p hV (countSafePayoff V M) (integerCountState X) := by
  have hs := integer_three_source V M p hV (countSafePayoff V M) X
  have hf : (fun Y : BoxState V M × IntegerCounters => countSafePayoff V M (integerCountState Y))=
      (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V M) (realCounterState Y))) := by
    funext Y
    exact count_safe_payoff_real V M Y
  rw [hf,integer_three_real V M p hV
    (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V M) Y)) X] at hs
  rw [real_three_joint_cycle V M p hV _ (FiniteKernel.eventIndicator_bounds _)] at hs
  exact hs.le.trans (source_cycle_transfer V M p hV _ (count_safe_payoff_bound V M)
    (count_safe_payoff_zero V M) (integerCountState X))

end
end FiniteReservoir
