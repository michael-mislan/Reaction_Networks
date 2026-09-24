import proofs.FiniteCopyReactor.SafeCycle
import proofs.FiniteCopyReactor.JointSourceBridge

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

def CountCycleSuccess (V : ℕ) (X : JointCounts) : Prop :=
  Restart V X.1 ∧
    (Nat.ceil ((V:ℝ)/56):ℝ) ≤ (X.2 1:ℝ) ∧ (Nat.ceil ((V:ℝ)/1080):ℝ) ≤ (X.2 0:ℝ) ∧
    (X.2 2:ℝ) ≤ 5*(V:ℝ) ∧ (X.2 3:ℝ) ≤ 5*(V:ℝ) ∧ (X.2 4:ℝ) ≤ (Nat.floor ((V:ℝ)/5):ℝ)

def CountSafeCycleSuccess (V : ℕ) (X : JointCounts) : Prop :=
  countSegmentActive true V X.1 ∧ CountCycleSuccess V X

def realSafeEvent (V : ℕ) : Set (BoxCounts V × ReactorCounters) :=
  {X | residenceActive V X.1 ∧ CycleSuccess V X}

def countSafePayoff (V : ℕ) (X : JointCounts) : ℝ≥0∞ := if CountSafeCycleSuccess V X then 1 else 0

theorem count_safe_payoff_bound (V : ℕ) (X : JointCounts) : countSafePayoff V X ≤ 1 := by
  unfold countSafePayoff
  split_ifs <;> simp

theorem count_safe_payoff_zero (V : ℕ) (X : JointCounts) (hx : X ∉ jointCountActive true V) :
    countSafePayoff V X=0 := if_neg (fun h => hx h.1)

theorem count_safe_payoff_real (V : ℕ) (X : BoxCounts V × IntegerCounters) :
    countSafePayoff V (integerCountState X)=
      ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V) (realCounterState X)) := by
  simp only [countSafePayoff, CountSafeCycleSuccess, CountCycleSuccess,
    integerCountState, countSegmentActive, if_true,
    FiniteKernel.eventIndicator, realSafeEvent, Set.mem_setOf_eq,
    residenceActive, CycleSuccess, realCounterState]
  split_ifs <;> simp

theorem safe_cycle_in_real_event (V : ℕ) (X : BoxCounts V × ReactorCounters) (h : SafeCycleSuccess V X) :
    X ∈ realSafeEvent V := by
  have hh := safe_cycle_success_properties V X h
  exact ⟨hh.2,hh.1⟩

theorem pulse_real_safe_bound (N : Counts) (V : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (r d : ℝ) (hV : 0 < (V:ℝ))
    (hr : 19 ≤ r) (hr' : r ≤ 21) (hd : 0 ≤ d) (hd' : d ≤ 1/25) :
    1-oneCycleError V ≤ pulseCycle N V p hN r d hV (by linarith) hr' hd hd'
      (FiniteKernel.eventIndicator (realSafeEvent V)) := by
  have hp := pulse_safe_success_bound N V p hN hlarge r d hV hr hr' hd hd'
  apply hp.trans
  apply pulse_cycle_mono N V p hN r d hV (by linarith) hr' hd hd' _ _ 1 1
    (FiniteKernel.eventIndicator_bounds _) (FiniteKernel.eventIndicator_bounds _)
  intro X
  unfold FiniteKernel.eventIndicator
  by_cases hx : SafeCycleSuccess V X
  · simp only [Set.mem_setOf_eq,hx,if_true,safe_cycle_in_real_event V X hx]
    exact le_rfl
  · simp only [Set.mem_setOf_eq,hx,if_false]
    split_ifs <;> norm_num

end
end FiniteCopyReactor
