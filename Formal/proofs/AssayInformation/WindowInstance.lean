import proofs.AssayInformation.WindowBands
import proofs.AssayInformation.DualMargin

noncomputable section
namespace AssayInformation
open DiagnosticWindows FiniteCopy

def safeBand : ErrorBand := ⟨0,1/100,0,1/20⟩
def excludedBand : ErrorBand := ⟨0,1,69/1000,1⟩

theorem source_probability_bounds (P : FiniteKernel (Fin 6)) (load t : NNReal) :
    0 ≤ 1-P.poissonized t uncalled 0 ∧ 1-P.poissonized t uncalled 0 ≤ 1 ∧
    0 ≤ loadedSurvival P load t ∧ loadedSurvival P load t ≤ 1 := by
  have he := P.poissonized_event_bounds t {x : Fin 6 | x ≠ 5} 0
  rw [← uncalled_indicator] at he
  refine ⟨by linarith [he.2],by linarith [he.1],?_,?_⟩
  · unfold loadedSurvival
    apply tsum_nonneg
    intro n
    apply mul_nonneg (poissonWeight_nonneg _ _)
    rw [uncalled_indicator]
    exact (P.poissonized_event_bounds _ _ _).1
  · unfold loadedSurvival
    rw [← (poissonWeight_sum load).tsum_eq]
    apply Summable.tsum_le_tsum
    · intro n
      apply mul_le_of_le_one_right (poissonWeight_nonneg _ _)
      rw [uncalled_indicator]
      exact (P.poissonized_event_bounds _ _ _).2
    · exact loading_summable _ _ _
    · exact (poissonWeight_sum _).summable

theorem three_decision_examples :
    (safeBand.Covers (blank10 (16/5)) (miss10 (16/5)) ∧ safeBand.Usable (1/100) (1/20)) ∧
    (coarseBand.Covers (blank10 (16/5)) (miss10 (16/5)) ∧ coarseBand.Unresolved (1/100) (1/20)) ∧
    (excludedBand.Covers (blank5 5) (miss5 5) ∧ excludedBand.Excluded (1/100) (1/20)) := by
  have h10 := source_probability_bounds kernel10 4 ((5/2)*(16/5))
  have h5 := source_probability_bounds kernel5 4 ((5/2)*5)
  change 0 ≤ blank10 (16/5) ∧ blank10 (16/5) ≤ 1 ∧
    0 ≤ miss10 (16/5) ∧ miss10 (16/5) ≤ 1 at h10
  change 0 ≤ blank5 5 ∧ blank5 5 ≤ 1 ∧ 0 ≤ miss5 5 ∧ miss5 5 ≤ 1 at h5
  have hg := capacity10_errors
  refine ⟨⟨?_,?_⟩,⟨?_,coarse_unresolved⟩,⟨?_,?_⟩⟩
  · exact ⟨h10.1,hg.1,h10.2.2.1,hg.2⟩
  · norm_num [safeBand,ErrorBand.Usable]
  · exact ⟨h10.1,by dsimp [coarseBand]; linarith [hg.1],h10.2.2.1,
      by dsimp [coarseBand]; linarith [hg.2]⟩
  · exact ⟨h5.1,h5.2.1,dual_miss_lower.le,h5.2.2.2⟩
  · norm_num [excludedBand,ErrorBand.Excluded]

end AssayInformation
