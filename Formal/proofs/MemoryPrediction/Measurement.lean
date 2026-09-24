import proofs.MemoryPrediction.YuleAmbiguity
import proofs.MemoryPrediction.Confidence

namespace MemoryPrediction
noncomputable section
open LowFounderPrediction MeasureTheory ProbabilityTheory

def menuLaw (independent : Bool) : Measure State :=
  if independent then independentSource else sharedSource
def lowIndicator (x : State) : ℝ := if totalCount x ≤ 2 then 1 else 0
def menuMean (independent : Bool) : ℝ := if independent then 9/16 else 5/8
def inferredIndependent {Ω : Type*} (O : Fin 4000 → Ω → State) (ω : Ω) : Bool :=
  decide (sampleMean (fun i ω => lowIndicator (O i ω)) ω < 19/32)
def chosenEndpoint {Ω : Type*} (O : Fin 4000 → Ω → State) (ω : Ω) : ℕ :=
  if inferredIndependent O ω then 6 else 7

theorem low_indicator_integral (μ : Measure State) :
    (∫ x,lowIndicator x ∂μ) = sourceCDF μ 2 := by
  have he : lowIndicator = Set.indicator {x : State | totalCount x ≤ 2} (fun _ => (1 : ℝ)) := by
    funext x
    simp [lowIndicator,Set.indicator]
  rw [he]
  exact integral_indicator_one (Set.to_countable _).measurableSet

theorem menu_indicator_mean (b : Bool) : (∫ x,lowIndicator x ∂menuLaw b) = menuMean b := by
  rw [low_indicator_integral]
  cases b
  · exact chronological_endpoint_table.2.1
  · exact chronological_endpoint_table.1

theorem observation_mean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (O : Ω → State) (hO : Measurable O) (b : Bool) (hlaw : μ.map O = menuLaw b) :
    (∫ ω,lowIndicator (O ω) ∂μ) = menuMean b := by
  rw [← integral_map hO.aemeasurable (measurable_of_countable lowIndicator).aestronglyMeasurable,
    hlaw,menu_indicator_mean]

/-- A singleton feasible model set can be selected from the actual two-founder
low-count observation. Its error probability is derived, not assumed. -/
theorem classification_error {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (O : Fin 4000 → Ω → State)
    (hO : ∀ i, Measurable (O i)) (hi : iIndepFun O μ)
    (b : Bool) (hlaw : ∀ i, μ.map (O i)=menuLaw b) :
    μ.real {ω | inferredIndependent O ω ≠ b} ≤ 1/2000 := by
  let X := fun i ω => lowIndicator (O i ω)
  have hm (i) : AEMeasurable (X i) μ :=
    ((measurable_of_countable lowIndicator).comp (hO i)).aemeasurable
  have hind : iIndepFun X μ := hi.comp (fun _ => lowIndicator) (fun _ => measurable_of_countable _)
  have hb (i) : ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp [X,lowIndicator]
    split_ifs <;> norm_num
  have hp (i) : ∫ ω,X i ω ∂μ = menuMean b := observation_mean μ (O i) (hO i) b (hlaw i)
  cases b
  · have h := bounded_sample_lower μ X (5/8) hm hind hb hp
    apply (measureReal_mono (μ := μ) (s₂ := {ω | sampleMean X ω ≤ 5/8-1/32}) ?_ (by finiteness)).trans h
    intro ω hω
    have hh : sampleMean X ω < 19/32 := by
      simpa [inferredIndependent,X] using hω
    change sampleMean X ω ≤ 5/8-1/32
    linarith
  · have h := bounded_sample_upper μ X (9/16) hm hind hb hp
    have he : {ω | inferredIndependent O ω ≠ true} = {ω | 9/16+1/32 ≤ sampleMean X ω} := by
      ext ω
      simp [inferredIndependent,X]
      norm_num
    rw [he]
    exact h

/-- Marginal source coverage and the proved classification error suffice: the
union bound does not require independence between calibration and the future. -/
theorem adaptive_prediction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (O : Fin 4000 → Ω → State)
    (hO : ∀ i, Measurable (O i)) (hi : iIndepFun O μ)
    (b : Bool) (hlaw : ∀ i, μ.map (O i)=menuLaw b)
    (Y : Ω → State) (hY : Measurable Y) (hfuture : μ.map Y=menuLaw b) :
    (153045/160000 : ℝ) ≤ μ.real {ω | totalCount (Y ω) ≤ chosenEndpoint O ω} := by
  have herr := classification_error μ O hO hi b hlaw
  let k : ℕ := if b then 6 else 7
  have hc : (245/256 : ℝ) ≤ μ.real {ω | totalCount (Y ω) ≤ k} := by
    have hm := map_measureReal_apply (μ := μ) hY
      (Set.to_countable {x : State | totalCount x ≤ k}).measurableSet
    rw [hfuture] at hm
    change (menuLaw b).real {x | totalCount x ≤ k} =
      μ.real {ω | totalCount (Y ω) ≤ k} at hm
    rw [← hm]
    cases b
    · change (245/256 : ℝ) ≤ sourceCDF sharedSource 7
      rw [chronological_endpoint_table.2.2.2.2.2]
      norm_num
    · change (245/256 : ℝ) ≤ sourceCDF independentSource 6
      rw [chronological_endpoint_table.2.2.2.1]
  have hs : {ω | totalCount (Y ω) ≤ k} ⊆
      {ω | totalCount (Y ω) ≤ chosenEndpoint O ω} ∪
        {ω | inferredIndependent O ω ≠ b} := by
    intro ω hω
    by_cases hb : inferredIndependent O ω = b
    · left
      simpa [chosenEndpoint,hb,k] using hω
    · exact Or.inr hb
  have ht := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)
  linarith

theorem adaptive_prediction_margin : (19/20 : ℝ) < 153045/160000 := by norm_num

end
end MemoryPrediction
