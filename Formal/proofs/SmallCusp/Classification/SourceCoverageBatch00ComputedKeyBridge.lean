import proofs.SmallCusp.Classification.SourceCoverageBatch00KeyIndexBridge
import proofs.SmallCusp.Classification.SourceCoverageRecordKeyIndexLemma

namespace SmallCusp

def sourceCoverageBatch00ComputedKeys : Array Nat :=
  sourceCoverageBatch00.toArray.map (fun R =>
    bimolCatalogueKey
      (Finset.univ.image (fun r => bimolReactionCatalogue (R.sourceIndices r))))

theorem source_coverage_batch00_computed_keys_match_literals :
    sourceCoverageBatch00ComputedKeys = sourceCoverageSourceKeys00 := by
  have hvalid : ∀ R ∈ sourceCoverageBatch00, R.Docked := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using
      sourceCoverageBatch00_valid
  have hmap :
      sourceCoverageBatch00.map (fun R =>
        bimolCatalogueKey
          (Finset.univ.image
            (fun r => bimolReactionCatalogue (R.sourceIndices r)))) =
      sourceCoverageBatch00.map (fun R =>
        sourceKeyFromIndexRow
          (Array.ofFn (fun i => (R.sourceIndices i).val))) := by
    apply List.map_congr_left
    intro R hR
    calc
      bimolCatalogueKey
          (Finset.univ.image
            (fun r => bimolReactionCatalogue (R.sourceIndices r))) =
          sourceCoverageRecordReducedKey R :=
        source_coverage_record_key_eq_reduced R (hvalid R hR).1
      _ = sourceKeyFromIndexRow
          (Array.ofFn (fun i => (R.sourceIndices i).val)) :=
        source_coverage_record_reduced_key_eq_index_row R
  have hmapArray :
      sourceCoverageBatch00ComputedKeys =
        sourceCoverageBatch00ReducedKeysFromIndexRows := by
    simpa [sourceCoverageBatch00ComputedKeys,
      sourceCoverageBatch00ReducedKeysFromIndexRows] using congrArg List.toArray hmap
  rw [hmapArray]
  exact source_coverage_batch00_reduced_keys_from_index_rows_match_literals

end SmallCusp
