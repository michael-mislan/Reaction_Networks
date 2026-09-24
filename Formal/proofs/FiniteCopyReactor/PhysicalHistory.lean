import proofs.FiniteCopyReactor.LiteralCycleBound
import proofs.FiniteCopyReactor.HistorySurvival
import proofs.FiniteCopyReactor.EffectiveScale

namespace FiniteCopyReactor
noncomputable section
open Classical ProductiveRecovery MeasureTheory ProbabilityTheory RandomViability RandomViability.Binding
open scoped ENNReal

/-- A history extension obeys the literal conditional cycle law. The history space
may include all observed times and labels; the current count state is its actual return. -/
structure PhysicalHistory (H : Type*) [MeasurableSpace H] (V : ℕ) (r d : ℝ)
    (hV : 0 < (V:ℝ)) (hr : 0 ≤ r) (hd : 0 ≤ d) where
  current : H → Counts
  observe : H → JointCounts
  observe_measurable : Measurable observe
  current_return : ∀ h,current h=(observe h).1
  policy : H → Intervention
  step : Kernel H H
  markov : IsMarkovKernel step
  conditional_law : ∀ h,(step h).map observe=literalPulseCycleMeasure (current h) V (policy h) r d hV hr hd

variable {H : Type*} [MeasurableSpace H]

def physicalHistorySuccess {V : ℕ} {r d : ℝ} {hV hr hd}
    (R : PhysicalHistory H V r d hV hr hd) : Set H := {h | CountCycleSuccess V (R.observe h)}

theorem physical_history_success_measurable {V : ℕ} {r d : ℝ} {hV hr hd}
    (R : PhysicalHistory H V r d hV hr hd) : MeasurableSet (physicalHistorySuccess R) :=
  R.observe_measurable ((Set.to_countable {X : JointCounts | CountCycleSuccess V X}).measurableSet)

theorem physical_history_one_cycle {V : ℕ} {r d : ℝ} {hV hr hd}
    (R : PhysicalHistory H V r d hV hr hd) (hlarge : 1000000 ≤ V)
    (hr19 : 19 ≤ r) (hr21 : r ≤ 21) (hd25 : d ≤ 1/25) (h : H) (hh : Restart V (R.current h)) :
    ENNReal.ofReal (1-oneCycleError V) ≤ R.step h (physicalHistorySuccess R) := by
  have hp := literal_cycle_success_bound (R.current h) V (R.policy h) hh hlarge r d hV hr19 hr21 hd hd25
  rw [← R.conditional_law h,Measure.map_apply R.observe_measurable
    (Set.to_countable {X : JointCounts | CountCycleSuccess V X}).measurableSet] at hp
  exact hp

/-- No independence of successive cycle successes is required. -/
theorem physical_history_success_lower {V : ℕ} {r d : ℝ} {hV hr hd}
    (R : PhysicalHistory H V r d hV hr hd) (hscale : 200000000000 ≤ V)
    (hr19 : 19 ≤ r) (hr21 : r ≤ 21) (hd25 : d ≤ 1/25) (n : ℕ) (h : H)
    (hh : Restart V (R.current h)) :
    ENNReal.ofReal (1-(n:ℝ)*oneCycleError V) ≤
      successfulHistoryKernel R.step (physicalHistorySuccess R) (physical_history_success_measurable R) n h Set.univ := by
  apply history_survival_linear R.step {y | Restart V (R.current y)} (physicalHistorySuccess R)
    (physical_history_success_measurable R) _ (oneCycleError V)
    _ (fun y hy => physical_history_one_cycle R (by omega) hr19 hr21 hd25 y hy) n h hh
  · intro y hy
    change Restart V (R.current y)
    rw [R.current_return y]
    exact hy.1
  · have hs := one_cycle_error_small V (by exact_mod_cast hscale)
    linarith

end
end FiniteCopyReactor
