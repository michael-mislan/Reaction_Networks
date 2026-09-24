import proofs.FiniteReservoir.CycleExpectations

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

theorem pulse_prepared_failure_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))
     :
    pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator (PreparedCycleFailure V M)) ≤ oneCycleError V := by
  let E := BadPulseStock N V p ∪ BadPulseMaterial N V p
  have hp (o : PulseOutcome N) :
      jointCycle V M params hV (FiniteKernel.eventIndicator (PreparedCycleFailure V M))
        (postPulse N V M p hN fuel o) (initialCounters (doseU V p) (doseW V p)) ≤
        (if o ∈ E then 1 else 0)+preparedCycleError V := by
    by_cases ho : o ∈ E
    · rw [if_pos ho]
      exact (joint_cycle_event_bounds V M params hV _ _ _).2.trans
        (le_add_of_nonneg_right (preparedCycleError_nonneg V))
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
      exact prepared_cycle_failure_bound V M params hV hlarge (postPulse N V M p hN fuel o) hs hm (doseU V p) (doseW V p)
        (pulse_food_budget V p).1 (pulse_food_budget V p).2
  have hsum := Finset.sum_le_sum (fun o (_ : o ∈ Finset.univ) => mul_le_mul_of_nonneg_left (hp o) (pulseMass_nonneg N p o))
  have he : (∑ o,pulseMass N p o*((if o ∈ E then 1 else 0)+preparedCycleError V))=
      pulseProbability N p E+preparedCycleError V := by
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

def SafeCycleSuccess (V M : ℕ) (X : BoxState V M × ReactorCounters) : Prop :=
  X ∉ PreparedCycleFailure V M

theorem safe_cycle_success_properties (V M : ℕ) (X : BoxState V M × ReactorCounters)
    (h : SafeCycleSuccess V M X) : CycleSuccess V M X ∧ residenceActive V X.1.1 := by
  refine ⟨outside_prepared_cycle_failure V M X h,?_⟩
  exact (outside_state_restart_failure V M X.1 (fun hn => h (Or.inr hn))).1

theorem pulse_safe_success_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))
     :
    1-oneCycleError V ≤ pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator {X | SafeCycleSuccess V M X}) := by
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
  have hf := pulse_prepared_failure_bound N V M p hN hlarge params fuel hV
  dsimp [A,B] at hadd
  linarith

end
end FiniteReservoir
