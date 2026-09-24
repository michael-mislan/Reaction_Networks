import proofs.FiniteReservoir.SafeCycle
import proofs.FiniteReservoir.JointSourceBridge

namespace FiniteReservoir
noncomputable section
open Classical FiniteCopyReactor ProductiveRecovery RandomViability.Binding FiniteCopy
open scoped ENNReal

def CountCycleSuccess (V M : ℕ) (X : JointCounts M) : Prop :=
  Restart V X.1.1 ∧
    (Nat.ceil ((V:ℝ)/56):ℝ) ≤ (X.2 1:ℝ) ∧ (Nat.ceil ((V:ℝ)/1080):ℝ) ≤ (X.2 0:ℝ) ∧
    (X.2 2:ℝ) ≤ 5*(V:ℝ) ∧ (X.2 3:ℝ) ≤ 5*(V:ℝ) ∧ (X.2 4:ℝ) ≤ (Nat.floor ((V:ℝ)/5):ℝ)

def CountSafeCycleSuccess (V M : ℕ) (X : JointCounts M) : Prop :=
  countSegmentActive true V X.1.1 ∧ CountCycleSuccess V M X

def realSafeEvent (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  {X | residenceActive V X.1.1 ∧ CycleSuccess V M X}

def countSafePayoff (V M : ℕ) (X : JointCounts M) : ℝ≥0∞ := if CountSafeCycleSuccess V M X then 1 else 0

theorem count_safe_payoff_bound (V M : ℕ) (X : JointCounts M) : countSafePayoff V M X ≤ 1 := by
  unfold countSafePayoff
  split_ifs <;> simp

theorem count_safe_payoff_zero (V M : ℕ) (X : JointCounts M) (hx : X ∉ jointCountActive true V M) :
    countSafePayoff V M X=0 := if_neg (fun h => hx h.1)

theorem count_safe_payoff_real (V M : ℕ) (X : BoxState V M × IntegerCounters) :
    countSafePayoff V M (integerCountState X)=
      ENNReal.ofReal (FiniteKernel.eventIndicator (realSafeEvent V M) (realCounterState X)) := by
  simp only [countSafePayoff, CountSafeCycleSuccess, CountCycleSuccess,
    integerCountState, countSegmentActive, if_true,
    FiniteKernel.eventIndicator, realSafeEvent, Set.mem_setOf_eq,
    residenceActive, CycleSuccess, realCounterState]
  split_ifs <;> simp

theorem safe_cycle_in_real_event (V M : ℕ) (X : BoxState V M × ReactorCounters) (h : SafeCycleSuccess V M X) :
    X ∈ realSafeEvent V M := by
  have hh := safe_cycle_success_properties V M X h
  exact ⟨hh.2,hh.1⟩

theorem pulse_real_safe_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))
     :
    1-oneCycleError V ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (realSafeEvent V M)) := by
  have hp := pulse_safe_success_bound N V M p hN hlarge params fuel hV
  apply hp.trans
  apply pulse_cycle_mono N V M p hN params fuel hV _ _ 1 1
    (FiniteKernel.eventIndicator_bounds _) (FiniteKernel.eventIndicator_bounds _)
  intro X
  unfold FiniteKernel.eventIndicator
  by_cases hx : SafeCycleSuccess V M X
  · simp only [Set.mem_setOf_eq,hx,if_true,safe_cycle_in_real_event V M X hx]
    exact le_rfl
  · simp only [Set.mem_setOf_eq,hx,if_false]
    split_ifs <;> norm_num

end
end FiniteReservoir
