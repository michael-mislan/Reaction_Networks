import proofs.FiniteReservoir.LiteralCycleBound
import proofs.FiniteReservoir.ErrorScale
import proofs.FiniteCopyReactor.HistorySurvival

namespace FiniteReservoir
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding FiniteCopyReactor
open scoped ENNReal

/-- Full-state conditional history: the bath supplied to the next cycle is its actual return. -/
structure PhysicalHistory (H : Type*) [MeasurableSpace H] (V M : ℕ) (params : Parameters M)
    (hV : 0 < (V:ℝ)) where
  current : H → CountState M
  observe : H → JointCounts M
  observe_measurable : Measurable observe
  current_return : ∀ h,current h=(observe h).1
  policy : H → Intervention
  step : Kernel H H
  markov : IsMarkovKernel step
  conditional_law : ∀ h,(step h).map observe=
    literalPulseCycleMeasure (current h).1 V M (policy h) params (current h).2 hV

variable {H : Type*} [MeasurableSpace H]

def physicalHistorySuccess {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) : Set H := {h | CountCycleSuccess V M (R.observe h)}

theorem physical_history_success_measurable {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) : MeasurableSet (physicalHistorySuccess R) :=
  R.observe_measurable ((Set.to_countable {X : JointCounts M | CountCycleSuccess V M X}).measurableSet)

theorem physical_history_one_cycle {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) (hlarge : 1000000 ≤ V)
    (h : H) (hh : Restart V (R.current h).1) :
    ENNReal.ofReal (1-oneCycleError V) ≤ R.step h (physicalHistorySuccess R) := by
  have hp := literal_cycle_success_bound (R.current h).1 V M (R.policy h) hh hlarge params (R.current h).2 hV
  rw [← R.conditional_law h,Measure.map_apply R.observe_measurable
    (Set.to_countable {X : JointCounts M | CountCycleSuccess V M X}).measurableSet] at hp
  exact hp

theorem physical_history_product {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) (hlarge : 1000000 ≤ V) (n : ℕ) (h : H)
    (hh : Restart V (R.current h).1) :
    ENNReal.ofReal (1-oneCycleError V)^n ≤
      successfulHistoryKernel R.step (physicalHistorySuccess R) (physical_history_success_measurable R) n h Set.univ := by
  apply history_survival_product R.step {y | Restart V (R.current y).1} (physicalHistorySuccess R)
    (physical_history_success_measurable R) _ _
    (fun y hy => physical_history_one_cycle R hlarge y hy) n h hh
  intro y hy
  change Restart V (R.current y).1
  rw [R.current_return y]
  exact hy.1

theorem physical_history_success_lower {V M : ℕ} {params : Parameters M} {hV}
    (R : PhysicalHistory H V M params hV) (hscale : 200000000000 ≤ V) (n : ℕ) (h : H)
    (hh : Restart V (R.current h).1) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      successfulHistoryKernel R.step (physicalHistorySuccess R) (physical_history_success_measurable R) n h Set.univ := by
  apply history_survival_linear R.step {y | Restart V (R.current y).1} (physicalHistorySuccess R)
    (physical_history_success_measurable R) _ (oneCycleError V)
    _ (fun y hy => physical_history_one_cycle R (by omega) y hy) n h hh
  · intro y hy
    change Restart V (R.current y).1
    rw [R.current_return y]
    exact hy.1
  · have hs := one_cycle_error_small V (by exact_mod_cast hscale)
    linarith

end
end FiniteReservoir
