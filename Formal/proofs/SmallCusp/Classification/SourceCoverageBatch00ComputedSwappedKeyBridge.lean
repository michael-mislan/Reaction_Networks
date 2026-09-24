import proofs.SmallCusp.Classification.SourceCoverageBatch00KeyIndexBridge
import proofs.SmallCusp.Classification.SourceCoverageRecordKeyIndexLemma

namespace SmallCusp

def sourceCoverageBatch00ComputedSwappedKeys : Array Nat :=
  sourceCoverageBatch00.toArray.map (fun R =>
    bimolCatalogueKey
      (swapBimolReactionSet
        (Finset.univ.image
          (fun r => bimolReactionCatalogue (R.sourceIndices r)))))

theorem source_coverage_batch00_computed_swapped_keys_match_literals :
    sourceCoverageBatch00ComputedSwappedKeys =
      sourceCoverageSourceKeysSwapped00 := by
  have hvalid : ∀ R ∈ sourceCoverageBatch00, R.Docked := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      sourceCoverageBatch00_valid
  have hmap :
      sourceCoverageBatch00.map (fun R =>
        bimolCatalogueKey
          (swapBimolReactionSet
            (Finset.univ.image
              (fun r => bimolReactionCatalogue (R.sourceIndices r))))) =
      sourceCoverageBatch00.map (fun R =>
        sourceSwappedKeyFromIndexRow
          (Array.ofFn (fun i => (R.sourceIndices i).val))) := by
    apply List.map_congr_left
    intro R hR
    calc
      bimolCatalogueKey
          (swapBimolReactionSet
            (Finset.univ.image
              (fun r => bimolReactionCatalogue (R.sourceIndices r)))) =
          sourceCoverageRecordReducedSwappedKey R :=
        source_coverage_record_swapped_key_eq_reduced R (hvalid R hR).1
      _ = sourceSwappedKeyFromIndexRow
          (Array.ofFn (fun i => (R.sourceIndices i).val)) :=
        source_coverage_record_reduced_swapped_key_eq_index_row R
  have hmapArray :
      sourceCoverageBatch00ComputedSwappedKeys =
        sourceCoverageBatch00.toArray.map (fun R =>
          sourceSwappedKeyFromIndexRow
            (Array.ofFn (fun i => (R.sourceIndices i).val))) := by
    simpa [sourceCoverageBatch00ComputedSwappedKeys] using congrArg List.toArray hmap
  rw [hmapArray]
  have hi : sourceCoverageBatch00IndexRows = sourceCoverageSourceIndices00 := by
    simpa [sourceCoverageBatch00IndexRowsValid] using
      source_coverage_batch00_indices_match_literals
  have hk : sourceCoverageSourceIndices00.map sourceSwappedKeyFromIndexRow =
      sourceCoverageSourceKeysSwapped00 := by
    have h := source_coverage_literal_index_keys_match
    simp only [sourceCoverageSourceIndices00KeysValid, Bool.and_eq_true] at h
    simpa using h.2
  rw [show (sourceCoverageBatch00.toArray.map (fun R =>
      sourceSwappedKeyFromIndexRow
        (Array.ofFn (fun i => (R.sourceIndices i).val))) =
      sourceCoverageBatch00IndexRows.map sourceSwappedKeyFromIndexRow) by
        simp [sourceCoverageBatch00IndexRows]]
  rw [hi]
  exact hk

end SmallCusp
