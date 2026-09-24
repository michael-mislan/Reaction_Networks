import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Kernel.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic

namespace RandomViability
open Classical MeasureTheory ProbabilityTheory
noncomputable section
set_option maxHeartbeats 30000
variable {α β : Type*} [Fintype β]

def jumpLabelPMF (rate : β → ℝ) (hr : ∀ b, 0 ≤ rate b) (ht : 0 < ∑ b, rate b) : PMF β :=
  PMF.ofFintype (fun b => ENNReal.ofReal (rate b/(∑ c, rate c))) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => div_nonneg (hr b) ht.le), ← Finset.sum_div]
    rw [div_self (ne_of_gt ht)]
    exact ENNReal.ofReal_one)

def jumpClockMeasure [MeasurableSpace β] (rate : β → ℝ)
    (hr : ∀ b, 0 ≤ rate b) (ht : 0 < ∑ b, rate b) : Measure (β × ℝ) :=
  (jumpLabelPMF rate hr ht).toMeasure.prod (expMeasure (∑ b, rate b))

instance jumpClockMeasure_probability [MeasurableSpace β] (rate : β → ℝ)
    (hr : ∀ b, 0 ≤ rate b) (ht : 0 < ∑ b, rate b) :
    IsProbabilityMeasure (jumpClockMeasure rate hr ht) := by
  letI := isProbabilityMeasure_expMeasure ht
  unfold jumpClockMeasure
  infer_instance

def jumpClockKernel [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) : Kernel α (β × ℝ) :=
  Kernel.ofFunOfCountable (fun x => jumpClockMeasure (rate x) (hr x) (ht x))

instance jumpClockKernel_markov [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (rate : α → β → ℝ)
    (hr : ∀ x b, 0 ≤ rate x b) (ht : ∀ x, 0 < ∑ b, rate x b) :
    IsMarkovKernel (jumpClockKernel rate hr ht) where
  isProbabilityMeasure x := jumpClockMeasure_probability (rate x) (hr x) (ht x)

end
end RandomViability
