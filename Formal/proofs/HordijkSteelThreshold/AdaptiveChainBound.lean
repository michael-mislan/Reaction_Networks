import proofs.HordijkSteelThreshold.AdaptiveMixtureBound

namespace HordijkSteelThreshold

open MeasureTheory ProbabilityTheory

/-- Weighted adaptive mixing.  If a fresh-block section has probability at
most `p` for every independently selected finite state, intersecting it with
an arbitrary event determined by that state costs a multiplicative factor
`p`.  This is the induction interface for ordered multi-target reveals. -/
theorem measure_adaptive_of_indep_finite_inter_le
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
    [MeasurableSpace β] [Fintype α] [MeasurableSingletonClass α]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → α} {Y : Ω → β} (hXY : IndepFun X Y μ)
    (hX : Measurable X)
    (K : α → Prop) (H : α → β → Prop)
    (hH : ∀ a, MeasurableSet {b | H a b}) {p : ENNReal}
    (hsec : ∀ a, μ {ω | H a (Y ω)} ≤ p) :
    μ {ω | K (X ω) ∧ H (X ω) (Y ω)} ≤
      p * μ {ω | K (X ω)} := by
  classical
  let I : Finset α := Finset.univ.filter K
  have hevent : {ω | K (X ω) ∧ H (X ω) (Y ω)} =
      ⋃ a ∈ I, X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b} := by
    ext ω
    simp [I, and_left_comm, and_comm]
  have hpre : X ⁻¹' (↑I : Set α) = {ω | K (X ω)} := by
    ext ω
    simp [I]
  have hsum : ∑ a ∈ I, μ (X ⁻¹' {a}) = μ {ω | K (X ω)} := by
    rw [← hpre]
    exact sum_measure_preimage_singleton I
      (fun a _ha => hX (measurableSet_singleton a))
  rw [hevent]
  calc
    μ (⋃ a ∈ I, X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b}) ≤
        ∑ a ∈ I, μ (X ⁻¹' {a} ∩ Y ⁻¹' {b | H a b}) :=
      measure_biUnion_finset_le _ _
    _ = ∑ a ∈ I, μ (X ⁻¹' {a}) * μ (Y ⁻¹' {b | H a b}) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact hXY.measure_inter_preimage_eq_mul {a} {b | H a b}
        (measurableSet_singleton a) (hH a)
    _ ≤ ∑ a ∈ I, μ (X ⁻¹' {a}) * p := by
      apply Finset.sum_le_sum
      intro a ha
      gcongr
      exact hsec a
    _ = (∑ a ∈ I, μ (X ⁻¹' {a})) * p := by
      rw [Finset.sum_mul]
    _ = p * μ {ω | K (X ω)} := by
      rw [hsum, mul_comm]

/-- Iterating weighted reveal estimates multiplies their section costs.  This
is the finite algebraic closure used after each probabilistic step has been
authenticated against the complementary restriction. -/
theorem measure_chain_le_prod
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (E : Nat → Set Ω) (p : Nat → ENNReal) (m : Nat)
    (hstep : ∀ j < m, μ (E (j + 1)) ≤ p j * μ (E j)) :
    μ (E m) ≤ (∏ j ∈ Finset.range m, p j) * μ (E 0) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        μ (E (m + 1)) ≤ p m * μ (E m) := hstep m (by omega)
        _ ≤ p m * ((∏ j ∈ Finset.range m, p j) * μ (E 0)) := by
          gcongr
          exact ih (fun j hj => hstep j (by omega))
        _ = (∏ j ∈ Finset.range (m + 1), p j) * μ (E 0) := by
          rw [Finset.prod_range_succ]
          ac_rfl

/-- Entropy bookkeeping for ordered target sequences: the union over all
length-`m` sequences from a finite alphabet costs at most `|α|^m`. -/
theorem measure_iUnion_fin_function_le
    {Ω α : Type*} [MeasurableSpace Ω] [Fintype α]
    (μ : Measure Ω) (m : Nat) (E : (Fin m → α) → Set Ω)
    {p : ENNReal} (hE : ∀ s, μ (E s) ≤ p) :
    μ (⋃ s, E s) ≤ ((Fintype.card α : Nat) ^ m : ENNReal) * p := by
  calc
    μ (⋃ s, E s) ≤ ∑ s, μ (E s) := measure_iUnion_fintype_le μ E
    _ ≤ ∑ _s : Fin m → α, p := by
      apply Finset.sum_le_sum
      intro s hs
      exact hE s
    _ = ((Fintype.card α : Nat) ^ m : ENNReal) * p := by
      simp

end HordijkSteelThreshold
