import proofs.FiniteReservoir.LiteralCycleBound
import proofs.FiniteReservoir.SharpService

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy MeasureTheory FiniteCopyReactor
open scoped ENNReal BigOperators

/-- Sharper gross-service failure for the pure bath at cleavage 1/50. -/
def SharpGrossFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) := {X | (V:ℝ)/10-1 ≤ X.2 4}

/-- The original joint failure union with one additional failure event, on the same law. -/
def SharpCycleFailure (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  PreparedCycleFailure V M ∪ SharpGrossFailure V M

def sharpCycleError (V : ℝ) : ℝ := oneCycleError V+Real.exp (-V/2000)

theorem joint_sharp_gross_tail (V R : ℕ) (p : Parameters R) (hV : 0 < (V:ℝ)) (hR : 0 < (R:ℝ))
    (hcapacity : p.capacity=R) (hd : p.cleavage=1/50) (hlarge : 1000000 ≤ V)
    (N : BoxState V R) (doseU doseW : ℝ) :
    jointCycle V R p hV
      (fun X => if (V:ℝ)/10-1 ≤ X.2 4 then 1 else 0) N (initialCounters doseU doseW) ≤
      Real.exp (-(V:ℝ)/2000) := by
  have he := joint_cycle_supply_marginal .gross V R p hV
    (MarkedKernel.eventIndicator {a | (V:ℝ)/10-1 ≤ a.2}) N (initialCounters doseU doseW)
  have h := pure_sharp_stopped_tail V R p hV hR hcapacity hd hlarge N
  convert he.le.trans h using 1

theorem pulse_sharp_failure_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator (SharpCycleFailure V R)) ≤ sharpCycleError V := by
  have h1 := pulse_prepared_failure_bound N V R p hN hlarge params fuel hV
  have h2 : pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator (SharpGrossFailure V R)) ≤ Real.exp (-(V:ℝ)/2000) := by
    have hs := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => mul_le_mul_of_nonneg_left
      (joint_sharp_gross_tail V R params hV hR hcapacity hd hlarge (postPulse N V R p hN fuel o)
        (doseU V p) (doseW V p)) (pulseMass_nonneg N p o))
    rw [← Finset.sum_mul,pulseMass_total,one_mul] at hs
    exact hs
  have hu : pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator (SharpCycleFailure V R)) ≤
      pulseCycle N V R p hN params fuel hV (FiniteKernel.eventIndicator (PreparedCycleFailure V R))+
      pulseCycle N V R p hN params fuel hV (FiniteKernel.eventIndicator (SharpGrossFailure V R)) := by
    unfold pulseCycle
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro o _
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left
      (joint_cycle_event_union V R params hV (PreparedCycleFailure V R) (SharpGrossFailure V R) _ _)
      (pulseMass_nonneg N p o)
  unfold sharpCycleError
  linarith

def SharpCycleSuccess (V M : ℕ) (X : BoxState V M × ReactorCounters) : Prop :=
  CycleSuccess V M X ∧ X.2 4 ≤ (Nat.floor ((V:ℝ)/10):ℝ)

def SharpSafeSuccess (V M : ℕ) (X : BoxState V M × ReactorCounters) : Prop :=
  X ∉ SharpCycleFailure V M

theorem sharp_safe_properties (V M : ℕ) (X : BoxState V M × ReactorCounters)
    (h : SharpSafeSuccess V M X) : SharpCycleSuccess V M X ∧ residenceActive V X.1.1 := by
  have hp : SafeCycleSuccess V M X := fun hn => h (Or.inl hn)
  have hh := safe_cycle_success_properties V M X hp
  have h4 : X.2 4 < (V:ℝ)/10-1 := by
    by_contra hn
    exact h (Or.inr (le_of_not_gt hn))
  exact ⟨⟨hh.1,(h4.trans (Nat.sub_one_lt_floor ((V:ℝ)/10))).le⟩,hh.2⟩

theorem pulse_sharp_safe_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    1-sharpCycleError V ≤ pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator {X | SharpSafeSuccess V R X}) := by
  let A : Set (BoxState V R × ReactorCounters) := {X | SharpSafeSuccess V R X}
  let B := SharpCycleFailure V R
  have he : (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=(fun _ => (1:ℝ)) := by
    funext X
    simp only [FiniteKernel.eventIndicator,A,B,SharpSafeSuccess,Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hadd : pulseCycle N V R p hN params fuel hV
      (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=
      pulseCycle N V R p hN params fuel hV (FiniteKernel.eventIndicator A)+
      pulseCycle N V R p hN params fuel hV (FiniteKernel.eventIndicator B) := by
    simp only [pulseCycle,joint_cycle_add V R params hV
      (FiniteKernel.eventIndicator A) (FiniteKernel.eventIndicator B) 1 1
      (FiniteKernel.eventIndicator_bounds A) (FiniteKernel.eventIndicator_bounds B),mul_add,Finset.sum_add_distrib]
  rw [he,pulse_cycle_const] at hadd
  have hf := pulse_sharp_failure_bound N V R p hN hlarge params fuel hV hR hcapacity hd
  dsimp [A,B] at hadd
  linarith

/-- Literal-count version of the sharper joint event. -/
def SharpCountCycleSuccess (V M : ℕ) (X : JointCounts M) : Prop :=
  CountCycleSuccess V M X ∧ (X.2 4:ℝ) ≤ (Nat.floor ((V:ℝ)/10):ℝ)

def SharpCountSafe (V M : ℕ) (X : JointCounts M) : Prop :=
  countSegmentActive true V X.1.1 ∧ SharpCountCycleSuccess V M X

def sharpRealSafeEvent (V M : ℕ) : Set (BoxState V M × ReactorCounters) :=
  {X | residenceActive V X.1.1 ∧ SharpCycleSuccess V M X}

def sharpSafePayoff (V M : ℕ) (X : JointCounts M) : ℝ≥0∞ := if SharpCountSafe V M X then 1 else 0

theorem sharp_safe_payoff_bound (V M : ℕ) (X : JointCounts M) : sharpSafePayoff V M X ≤ 1 := by
  unfold sharpSafePayoff
  split_ifs <;> simp

theorem sharp_safe_payoff_zero (V M : ℕ) (X : JointCounts M) (hx : X ∉ jointCountActive true V M) :
    sharpSafePayoff V M X=0 := if_neg (fun h => hx h.1)

theorem sharp_safe_payoff_real (V M : ℕ) (X : BoxState V M × IntegerCounters) :
    sharpSafePayoff V M (integerCountState X)=
      ENNReal.ofReal (FiniteKernel.eventIndicator (sharpRealSafeEvent V M) (realCounterState X)) := by
  simp only [sharpSafePayoff, SharpCountSafe, SharpCountCycleSuccess, CountCycleSuccess,
    integerCountState, countSegmentActive, if_true,
    FiniteKernel.eventIndicator, sharpRealSafeEvent, Set.mem_setOf_eq,
    residenceActive, SharpCycleSuccess, CycleSuccess, realCounterState]
  split_ifs <;> simp

theorem pulse_sharp_real_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    1-sharpCycleError V ≤ pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator (sharpRealSafeEvent V R)) := by
  have hp := pulse_sharp_safe_bound N V R p hN hlarge params fuel hV hR hcapacity hd
  apply hp.trans
  apply pulse_cycle_mono N V R p hN params fuel hV _ _ 1 1
    (FiniteKernel.eventIndicator_bounds _) (FiniteKernel.eventIndicator_bounds _)
  intro X
  unfold FiniteKernel.eventIndicator
  by_cases hx : SharpSafeSuccess V R X
  · have hm : X ∈ sharpRealSafeEvent V R :=
      ⟨(sharp_safe_properties V R X hx).2,(sharp_safe_properties V R X hx).1⟩
    simp only [Set.mem_setOf_eq,hx,if_true,hm]
    exact le_rfl
  · simp only [Set.mem_setOf_eq,hx,if_false]
    split_ifs <;> norm_num

theorem joint_sharp_source_lower (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (X : BoxState V M × IntegerCounters) :
    ENNReal.ofReal (jointCycle V M p hV
      (FiniteKernel.eventIndicator (sharpRealSafeEvent V M)) X.1 (realCounterState X).2) ≤
      jointSourceCycle V M p hV (sharpSafePayoff V M) (integerCountState X) := by
  have hs := integer_three_source V M p hV (sharpSafePayoff V M) X
  have hf : (fun Y : BoxState V M × IntegerCounters => sharpSafePayoff V M (integerCountState Y))=
      (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (sharpRealSafeEvent V M) (realCounterState Y))) := by
    funext Y
    exact sharp_safe_payoff_real V M Y
  rw [hf,integer_three_real V M p hV
    (fun Y => ENNReal.ofReal (FiniteKernel.eventIndicator (sharpRealSafeEvent V M) Y)) X] at hs
  rw [real_three_joint_cycle V M p hV _ (FiniteKernel.eventIndicator_bounds _)] at hs
  exact hs.le.trans (source_cycle_transfer V M p hV _ (sharp_safe_payoff_bound V M)
    (sharp_safe_payoff_zero V M) (integerCountState X))

theorem pulse_sharp_source_lower (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    ENNReal.ofReal (pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (sharpRealSafeEvent V M))) ≤
      sourcePulseCycle N V M p params fuel hV (sharpSafePayoff V M) := by
  unfold pulseCycle sourcePulseCycle
  rw [ENNReal.ofReal_sum_of_nonneg (fun o _ => mul_nonneg (pulseMass_nonneg N p o)
    (joint_cycle_event_bounds V M params hV _ _ _).1)]
  apply Finset.sum_le_sum
  intro o _
  rw [ENNReal.ofReal_mul (pulseMass_nonneg N p o)]
  apply mul_le_mul_right
  have hh := joint_sharp_source_lower V M params hV
    (postPulse N V M p hN fuel o,integerInitialCounters (doseU V p) (doseW V p))
  simpa only [integerCountState,postPulse,postPulseBox_counts,pulseInitialState,
    realCounterState,integer_initial_counters_exact] using hh

/-- Uniform one-cycle bound for the literal pure-bath source with the halved service allowance. -/
theorem literal_sharp_cycle_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    ENNReal.ofReal (1-sharpCycleError V) ≤
      literalPulseCycleMeasure N V R p params fuel hV {X | SharpCountCycleSuccess V R X} := by
  rw [← actual_cycle_measure_literal]
  have hh := (ENNReal.ofReal_le_ofReal
    (pulse_sharp_real_bound N V R p hN hlarge params fuel hV hR hcapacity hd)).trans
    (pulse_sharp_source_lower N V R p hN params fuel hV)
  have he := actual_pulse_event N V R p params fuel hV {X | SharpCountSafe V R X}
  exact (hh.trans_eq he).trans (measure_mono (fun _ h => h.2))

end
end FiniteReservoir
