import proofs.FiniteReservoir.JointProbability
import proofs.FiniteReservoir.PulseMaterial
import proofs.FiniteCopyReactor.Preparation

namespace FiniteReservoir
noncomputable section
open ProductiveRecovery RandomViability.Binding FiniteCopy FiniteCopyReactor Classical
open scoped BigOperators

/-- Literal full molecule pulse, followed by the retained-state count cycle.
No pulse outcome is rejected. -/
def pulseCycle (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ)) 
    (f : BoxState V M × ReactorCounters → ℝ) : ℝ :=
  ∑ o,pulseMass N p o*jointCycle V M params hV f (postPulse N V M p hN fuel o)
    (initialCounters (doseU V p) (doseW V p))

def oneCycleError (V : ℝ) : ℝ :=
  Real.exp (-(1177/1000000000)*V)+4*Real.exp (-V/100000)+preparedCycleError V

theorem preparedCycleError_nonneg (V : ℕ) : 0 ≤ preparedCycleError V := by
  unfold preparedCycleError jointCounterError stateRestartError freeCollectionError freeDiscreteError
    collectionResidenceError materialExitError
  positivity

theorem pulse_cycle_failure_bound (N : Counts) (V M : ℕ) (p : Intervention) (hN : Restart V N)
    (hlarge : 1000000 ≤ V) (params : Parameters M) (fuel : FuelState M) (hV : 0 < (V:ℝ))
     :
    pulseCycle N V M p hN params fuel hV
      (FiniteKernel.eventIndicator {X | ¬CycleSuccess V M X}) ≤ oneCycleError V := by
  let E := BadPulseStock N V p ∪ BadPulseMaterial N V p
  have hp (o : PulseOutcome N) :
      jointCycle V M params hV (FiniteKernel.eventIndicator {X | ¬CycleSuccess V M X})
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
      exact prepared_success_failure_bound V M params hV hlarge (postPulse N V M p hN fuel o) hs hm (doseU V p) (doseW V p)
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

end
end FiniteReservoir
