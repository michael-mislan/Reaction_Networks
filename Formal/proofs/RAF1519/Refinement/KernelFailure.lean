import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Bad preparations retain their full probability; good inputs pay the conditional error. -/
theorem kernel_failure_bound {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (κ : Kernel α β) [IsMarkovKernel κ]
    (Bad : Set α) (hBad : MeasurableSet Bad) (E : Set β) (hE : MeasurableSet E)
    (ε : ℝ≥0∞) (hgood : ∀ x ∉ Bad, κ x E ≤ ε) :
    (κ ∘ₘ μ) E ≤ μ Bad+ε := by
  rw [Measure.bind_apply hE κ.aemeasurable]
  calc
    _ ≤ ∫⁻ x, Bad.indicator (1 : α → ℝ≥0∞) x+ε ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      by_cases hx : x ∈ Bad
      · rw [Set.indicator_of_mem hx]
        exact prob_le_one.trans (le_add_right le_rfl)
      · rw [Set.indicator_of_notMem hx,zero_add]
        exact hgood x hx
    _ = _ := by
      rw [lintegral_add_right _ measurable_const,lintegral_indicator_one hBad,lintegral_const,measure_univ,mul_one]

end
end RAF1519.Refinement
