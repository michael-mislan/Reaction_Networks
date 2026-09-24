import proofs.MemoryPrediction.Resolution

namespace MemoryPrediction
noncomputable section
open MeasureTheory ProbabilityTheory LowFounderPrediction

theorem nested_endpoint_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N K : Ω → ℕ)
    (hK : ∀ ω, 6 ≤ K ω) :
    μ.real {ω | N ω ≤ 6} ≤ μ.real {ω | N ω ≤ K ω} := by
  exact measureReal_mono (fun ω hω => hω.trans (hK ω))

theorem upper_endpoint_loss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (N K : Ω → ℕ)
    (hK : ∀ ω, K ω = 6 ∨ K ω = 7) :
    μ.real {ω | N ω ≤ 7} ≤
      μ.real {ω | N ω ≤ K ω} + μ.real {ω | K ω = 6} := by
  have hs : {ω | N ω ≤ 7} ⊆ {ω | N ω ≤ K ω} ∪ {ω | K ω = 6} := by
    intro ω hω
    rcases hK ω with h | h
    · exact Or.inr h
    · exact Or.inl (by simpa [h] using hω)
  exact (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)

/-- Direction-aware improvement: errors under I enlarge the endpoint, so only
the W error can lower coverage. No calibration/future independence is needed. -/
theorem adaptive_prediction_sharp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (O : Fin 4000 → Ω → State)
    (hO : ∀ i, Measurable (O i)) (hi : iIndepFun O μ)
    (b : Bool) (hlaw : ∀ i, μ.map (O i)=menuLaw b)
    (Y : Ω → State) (hY : Measurable Y) (hfuture : μ.map Y=menuLaw b) :
    (245/256 : ℝ) ≤ μ.real {ω | totalCount (Y ω) ≤ chosenEndpoint O ω} := by
  have hf (k : ℕ) : sourceCDF (menuLaw b) k =
      μ.real {ω | totalCount (Y ω) ≤ k} := by
    have h := map_measureReal_apply (μ := μ) hY
      (Set.to_countable {x : State | totalCount x ≤ k}).measurableSet
    rw [hfuture] at h
    exact h
  have hk (ω) : chosenEndpoint O ω = 6 ∨ chosenEndpoint O ω = 7 := by
    unfold chosenEndpoint
    split_ifs <;> simp
  cases b
  · have herr := classification_error μ O hO hi false hlaw
    have he : {ω | chosenEndpoint O ω = 6} =
        {ω | inferredIndependent O ω ≠ false} := by
      ext ω
      simp [chosenEndpoint]
    have h := upper_endpoint_loss μ (fun ω => totalCount (Y ω)) (chosenEndpoint O) hk
    rw [he, ← hf 7] at h
    change sourceCDF sharedSource 7 ≤ _ at h
    rw [chronological_endpoint_table.2.2.2.2.2] at h
    linarith
  · have h := nested_endpoint_lower μ (fun ω => totalCount (Y ω)) (chosenEndpoint O)
      (fun ω => by rcases hk ω with h | h <;> omega)
    rw [← hf 6] at h
    change sourceCDF independentSource 6 ≤ _ at h
    rw [chronological_endpoint_table.2.2.2.1] at h
    exact h

end
end MemoryPrediction
