import proofs.FiniteReservoir.SharpPhase
import proofs.FiniteReservoir.SharpCycle

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery RandomViability.Binding FiniteCopy MeasureTheory FiniteCopyReactor
open scoped ENNReal BigOperators

def sharpJointCounterError (V : ℝ) : ℝ :=
  sharpFreeCollectionError V+Real.exp (-V/100000)+2*Real.exp (-V/300)+Real.exp (-V/2000)

/-- The original joint counter failure set, with the unrounded phase rate in its bound. -/
theorem joint_counter_budget_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ)) (hlarge : 1000000 ≤ V)
    (N : BoxState V M) (doseU doseW : ℝ)
    (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (FiniteKernel.eventIndicator (JointCounterFailure V M)) N (initialCounters doseU doseW) ≤
      sharpJointCounterError V := by
  let C := fun A => jointCycle V M p hV (FiniteKernel.eventIndicator A) N (initialCounters doseU doseW)
  have h0 : C (FreeCounterFailure V M) ≤ sharpFreeCollectionError V := by
    convert joint_free_tail_sharp V M p hV hlarge N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator FreeCounterFailure
    split_ifs <;> simp_all
  have h1 : C (TemplateCounterFailure V M) ≤ Real.exp (-(V:ℝ)/100000) := by
    convert joint_template_tail V M p hV hlarge N doseU doseW using 1
    unfold C
    congr 1
    funext X
    unfold FiniteKernel.eventIndicator TemplateCounterFailure
    split_ifs <;> simp_all
  have h2 : C (FoodUCounterFailure V M) ≤ Real.exp (-(V:ℝ)/300) := joint_foodU_tail V M p hV N doseU doseW hu
  have h3 : C (FoodWCounterFailure V M) ≤ Real.exp (-(V:ℝ)/300) := joint_foodW_tail V M p hV N doseU doseW hw
  have h4 : C (GrossCounterFailure V M) ≤ Real.exp (-(V:ℝ)/2000) := joint_rounded_gross_tail V M p hV hlarge N doseU doseW
  have hU (A B) : C (A ∪ B) ≤ C A+C B := joint_cycle_event_union V M p hV A B N (initialCounters doseU doseW)
  have h01 := hU (FreeCounterFailure V M) (TemplateCounterFailure V M)
  have h23 := hU (FoodUCounterFailure V M) (FoodWCounterFailure V M)
  have h234 := hU (FoodUCounterFailure V M ∪ FoodWCounterFailure V M) (GrossCounterFailure V M)
  have hall := hU (FreeCounterFailure V M ∪ TemplateCounterFailure V M)
    ((FoodUCounterFailure V M ∪ FoodWCounterFailure V M) ∪ GrossCounterFailure V M)
  change C _ ≤ _
  unfold JointCounterFailure sharpJointCounterError
  linarith

def sharpPreparedError (V : ℝ) : ℝ := sharpJointCounterError V+stateRestartError V

theorem prepared_cycle_failure_bound_sharp (V M : ℕ) (p : Parameters M) (hV : 0 < (V:ℝ))
    (hlarge : 1000000 ≤ V) (N : BoxState V M)
    (hstock : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts N.1))
    (hprep : ∀ side, (24/25)*(V:ℝ) ≤ unitObs side (boxCounts N.1) ∧ unitObs side (boxCounts N.1) ≤ (51/50)*(V:ℝ))
    (doseU doseW : ℝ) (hu : doseU ≤ (151/200)*(V:ℝ)) (hw : doseW ≤ (151/200)*(V:ℝ)) :
    jointCycle V M p hV
      (FiniteKernel.eventIndicator (PreparedCycleFailure V M)) N (initialCounters doseU doseW) ≤
      sharpPreparedError V := by
  have hU := joint_cycle_event_union V M p hV
    (JointCounterFailure V M) {X | X.1 ∈ StateRestartFailure V M} N (initialCounters doseU doseW)
  have hC := joint_counter_budget_sharp V M p hV hlarge N doseU doseW hu hw
  have hS := state_restart_failure_bound V M p hV N hstock hprep
  have hM := joint_state_marginal V M p hV
    (FiniteKernel.eventIndicator (StateRestartFailure V M)) N doseU doseW
  have hS' : jointCycle V M p hV
      (FiniteKernel.eventIndicator {X | X.1 ∈ StateRestartFailure V M}) N (initialCounters doseU doseW) ≤
      stateRestartError V := hM.le.trans hS
  exact hU.trans (add_le_add hC hS')

def sharpOneCycleError (V : ℝ) : ℝ :=
  Real.exp (-(1177/1000000000)*V)+4*Real.exp (-V/100000)+sharpPreparedError V

theorem sharpPreparedError_nonneg (V : ℕ) : 0 ≤ sharpPreparedError V := by
  unfold sharpPreparedError sharpJointCounterError stateRestartError sharpFreeCollectionError
    sharpFreeDiscreteError collectionResidenceError materialExitError
  positivity

theorem pulse_prepared_failure_bound_sharp (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (PreparedCycleFailure V M)) ≤ sharpOneCycleError V := by
  let E := BadPulseStock N V p ∪ BadPulseMaterial N V p
  have hp (o : PulseOutcome N) :
      jointCycle V M params hV (FiniteKernel.eventIndicator (PreparedCycleFailure V M))
        (postPulse N V M p hN fuel o) (initialCounters (doseU V p) (doseW V p)) ≤
        (if o ∈ E then 1 else 0)+sharpPreparedError V := by
    by_cases ho : o ∈ E
    · rw [if_pos ho]
      exact (joint_cycle_event_bounds V M params hV _ _ _).2.trans
        (le_add_of_nonneg_right (sharpPreparedError_nonneg V))
    · rw [if_neg ho,zero_add]
      have hs : (3/250)*(V:ℝ) ≤ weightedCount (boxCounts (postPulseBox N V p hN o)) := by
        rw [postPulseBox_counts]
        have hn : ¬weightedCount (postPulseCounts N V p o) ≤ (3/250)*(V:ℝ) := fun h => ho (Or.inl h)
        exact (lt_of_not_ge hn).le
      have hm (side : Bool) : (24/25)*(V:ℝ) ≤ unitObs side (boxCounts (postPulseBox N V p hN o)) ∧
          unitObs side (boxCounts (postPulseBox N V p hN o)) ≤ (51/50)*(V:ℝ) := by
        rw [postPulseBox_counts]
        have hn : ¬(unitObs side (postPulseCounts N V p o) < (24/25)*(V:ℝ) ∨
            (51/50)*(V:ℝ) < unitObs side (postPulseCounts N V p o)) := fun h => ho (Or.inr ⟨side,h⟩)
        constructor <;> by_contra h <;> apply hn <;> simp_all
      exact prepared_cycle_failure_bound_sharp V M params hV hlarge (postPulse N V M p hN fuel o) hs hm
        (doseU V p) (doseW V p) (pulse_food_budget V p).1 (pulse_food_budget V p).2
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hp o) (pulseMass_nonneg N p o))
  have he : (∑ o,pulseMass N p o*((if o ∈ E then 1 else 0)+sharpPreparedError V))=
      pulseProbability N p E+sharpPreparedError V := by
    simp only [mul_add,Finset.sum_add_distrib]
    rw [← Finset.sum_mul,pulseMass_total,one_mul]
    congr 1
    unfold pulseProbability
    apply Finset.sum_congr rfl
    intro o _
    split_ifs <;> simp
  rw [he] at hsum
  have hE := (pulseProbability_union N p (BadPulseStock N V p) (BadPulseMaterial N V p)).trans
    (add_le_add (pulse_stock_probability N V p hN)
      (pulse_material_probability N V p (by omega) hN))
  exact hsum.trans (add_le_add hE le_rfl)

/-- Any stopped bound for the original failure union transfers to the literal physical cycle. -/
theorem literal_cycle_bound_of (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) (ε : ℝ)
    (hf : pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (PreparedCycleFailure V M)) ≤ ε) :
    ENNReal.ofReal (1-ε) ≤
      literalPulseCycleMeasure N V M p params fuel hV {X | CountCycleSuccess V M X} := by
  let A : Set (BoxState V M × ReactorCounters) := {X | SafeCycleSuccess V M X}
  let B := PreparedCycleFailure V M
  have he : (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=(fun _ => (1:ℝ)) := by
    funext X
    simp only [FiniteKernel.eventIndicator,A,B,SafeCycleSuccess,Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hadd : pulseCycle N V M p hN params fuel hV
      (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=
      pulseCycle N V M p hN params fuel hV (FiniteKernel.eventIndicator A)+
      pulseCycle N V M p hN params fuel hV (FiniteKernel.eventIndicator B) := by
    simp only [pulseCycle,joint_cycle_add V M params hV
      (FiniteKernel.eventIndicator A) (FiniteKernel.eventIndicator B) 1 1
      (FiniteKernel.eventIndicator_bounds A) (FiniteKernel.eventIndicator_bounds B),mul_add,Finset.sum_add_distrib]
  rw [he,pulse_cycle_const] at hadd
  dsimp [A,B] at hadd
  have hsafe : 1-ε ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator {X | SafeCycleSuccess V M X}) := by linarith
  have hreal : 1-ε ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (realSafeEvent V M)) := by
    apply hsafe.trans
    apply pulse_cycle_mono N V M p hN params fuel hV _ _ 1 1
      (FiniteKernel.eventIndicator_bounds _) (FiniteKernel.eventIndicator_bounds _)
    intro X
    unfold FiniteKernel.eventIndicator
    by_cases hx : SafeCycleSuccess V M X
    · simp only [Set.mem_setOf_eq,hx,if_true,safe_cycle_in_real_event V M X hx]
      exact le_rfl
    · simp only [Set.mem_setOf_eq,hx,if_false]
      split_ifs <;> norm_num
  rw [← actual_cycle_measure_literal]
  have hh := (ENNReal.ofReal_le_ofReal hreal).trans
    (pulse_safe_source_lower N V M p hN params fuel hV)
  have hev := actual_pulse_event N V M p params fuel hV {X | CountSafeCycleSuccess V M X}
  exact (hh.trans_eq hev).trans (measure_mono (fun _ h => h.2))

/-- The same transfer for the union with the sharper gross-service failure. -/
theorem literal_sharp_cycle_bound_of (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) (ε : ℝ)
    (hf : pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (SharpCycleFailure V M)) ≤ ε) :
    ENNReal.ofReal (1-ε) ≤
      literalPulseCycleMeasure N V M p params fuel hV {X | SharpCountCycleSuccess V M X} := by
  let A : Set (BoxState V M × ReactorCounters) := {X | SharpSafeSuccess V M X}
  let B := SharpCycleFailure V M
  have he : (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=(fun _ => (1:ℝ)) := by
    funext X
    simp only [FiniteKernel.eventIndicator,A,B,SharpSafeSuccess,Set.mem_setOf_eq]
    split_ifs <;> simp_all
  have hadd : pulseCycle N V M p hN params fuel hV
      (fun X => FiniteKernel.eventIndicator A X+FiniteKernel.eventIndicator B X)=
      pulseCycle N V M p hN params fuel hV (FiniteKernel.eventIndicator A)+
      pulseCycle N V M p hN params fuel hV (FiniteKernel.eventIndicator B) := by
    simp only [pulseCycle,joint_cycle_add V M params hV
      (FiniteKernel.eventIndicator A) (FiniteKernel.eventIndicator B) 1 1
      (FiniteKernel.eventIndicator_bounds A) (FiniteKernel.eventIndicator_bounds B),mul_add,Finset.sum_add_distrib]
  rw [he,pulse_cycle_const] at hadd
  dsimp [A,B] at hadd
  have hsafe : 1-ε ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator {X | SharpSafeSuccess V M X}) := by linarith
  have hreal : 1-ε ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (sharpRealSafeEvent V M)) := by
    apply hsafe.trans
    apply pulse_cycle_mono N V M p hN params fuel hV _ _ 1 1
      (FiniteKernel.eventIndicator_bounds _) (FiniteKernel.eventIndicator_bounds _)
    intro X
    unfold FiniteKernel.eventIndicator
    by_cases hx : SharpSafeSuccess V M X
    · have hm : X ∈ sharpRealSafeEvent V M :=
        ⟨(sharp_safe_properties V M X hx).2,(sharp_safe_properties V M X hx).1⟩
      simp only [Set.mem_setOf_eq,hx,if_true,hm]
      exact le_rfl
    · simp only [Set.mem_setOf_eq,hx,if_false]
      split_ifs <;> norm_num
  rw [← actual_cycle_measure_literal]
  have hh := (ENNReal.ofReal_le_ofReal hreal).trans
    (pulse_sharp_source_lower N V M p hN params fuel hV)
  have hev := actual_pulse_event N V M p params fuel hV {X | SharpCountSafe V M X}
  exact (hh.trans_eq hev).trans (measure_mono (fun _ h => h.2))

/-- One-cycle error with both refinements: unrounded phase rate and the extra sharp-service event. -/
def sharpBothError (V : ℝ) : ℝ := sharpOneCycleError V+Real.exp (-V/2000)

theorem pulse_both_failure_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    pulseCycle N V R p hN params fuel hV
      (FiniteKernel.eventIndicator (SharpCycleFailure V R)) ≤ sharpBothError V := by
  have h1 := pulse_prepared_failure_bound_sharp N V R p hN hlarge params fuel hV
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
  unfold sharpBothError
  linarith

/-- All admitted baths: literal one-cycle success with the unrounded phase rate. -/
theorem literal_cycle_phase_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) :
    ENNReal.ofReal (1-sharpOneCycleError V) ≤
      literalPulseCycleMeasure N V M p params fuel hV {X | CountCycleSuccess V M X} :=
  literal_cycle_bound_of N V M p hN params fuel hV _
    (pulse_prepared_failure_bound_sharp N V M p hN hlarge params fuel hV)

/-- Pure bath at cleavage 1/50: both refinements on one literal cycle event. -/
theorem literal_both_cycle_bound (N : Counts) (V R : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters R) (fuel : FuelState R) (hV : 0 < (V:ℝ))
    (hR : 0 < (R:ℝ)) (hcapacity : params.capacity=R) (hd : params.cleavage=1/50) :
    ENNReal.ofReal (1-sharpBothError V) ≤
      literalPulseCycleMeasure N V R p params fuel hV {X | SharpCountCycleSuccess V R X} :=
  literal_sharp_cycle_bound_of N V R p hN params fuel hV _
    (pulse_both_failure_bound N V R p hN hlarge params fuel hV hR hcapacity hd)

end
end FiniteReservoir
