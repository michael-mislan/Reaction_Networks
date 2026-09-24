import proofs.RAF1519.Refinement.CategoricalEvent

namespace RAF1519.Refinement
noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal
set_option maxHeartbeats 30000

theorem categoricalPMF_event {ι : Type*} [Fintype ι]
    [MeasurableSpace (ι → Fin 3)] [MeasurableSingletonClass (ι → Fin 3)]
    (c : ι → Fin 3 → ℝ) (hc : ∀ m a, 0 ≤ c m a) (ht : ∀ m, ∑ a, c m a=1)
    (E : Set (ι → Fin 3)) :
    (categoricalPMF c hc ht).toMeasure E=ENNReal.ofReal (categoricalProbability c E) := by
  rw [(categoricalPMF c hc ht).toMeasure_apply (Set.to_countable E).measurableSet,tsum_fintype]
  have hn : ∀ o : ι → Fin 3, o ∈ Finset.univ → 0 ≤ (if o ∈ E then categoricalMass c o else 0) := by
    intro o _
    split_ifs
    · exact categoricalMass_nonneg c hc o
    · exact le_rfl
  rw [categoricalProbability,ENNReal.ofReal_sum_of_nonneg hn]
  apply Finset.sum_congr rfl
  intro o _
  by_cases ho : o ∈ E
  · rw [Set.indicator_of_mem ho,if_pos ho]
    exact PMF.ofFintype_apply _ o
  · rw [Set.indicator_of_notMem ho,if_neg ho,ENNReal.ofReal_zero]

end
end RAF1519.Refinement
