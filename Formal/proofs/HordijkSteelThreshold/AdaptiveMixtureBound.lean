import Mathlib.Probability.Independence.Basic

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory

/-- A finite state selected independently of a fresh block does not incur a
union-bound entropy penalty: a uniform fixed-state bad-event bound survives
adaptive mixing over the independent state. -/
theorem measure_adaptive_of_indep_finite
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hXY : IndepFun X Y μ)
    (hX : Measurable X)
    (H : α → β → Prop)
    (hH : ∀ a, MeasurableSet {b | H a b}) {p : ENNReal}
    (hsec : ∀ a, μ {ω | H a (Y ω)} ≤ p) :
    μ {ω | H (X ω) (Y ω)} ≤ p := by
  rw [show {ω | H (X ω) (Y ω)} =
      ⋃ a ∈ (Finset.univ : Finset α),
        X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b} by
      ext ω
      simp]
  calc
    μ (⋃ a ∈ (Finset.univ : Finset α),
        X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b}) ≤
        ∑ a ∈ (Finset.univ : Finset α),
          μ (X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b}) :=
      measure_biUnion_finset_le _ _
    _ = ∑ a ∈ (Finset.univ : Finset α),
        μ (X ⁻¹' {a}) * μ (Y ⁻¹' {b | H a b}) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hXY.measure_inter_preimage_eq_mul {a} {b | H a b}
        (measurableSet_singleton a) (hH a)
    _ ≤ ∑ a ∈ (Finset.univ : Finset α), μ (X ⁻¹' {a}) * p := by
      apply Finset.sum_le_sum
      intro a ha
      gcongr
      exact hsec a
    _ = (∑ a ∈ (Finset.univ : Finset α), μ (X ⁻¹' {a})) * p := by
      rw [Finset.sum_mul]
    _ = p := by
      rw [sum_measure_preimage_singleton]
      · simp
      · intro a ha
        exact hX (measurableSet_singleton a)

end HordijkSteelThreshold
