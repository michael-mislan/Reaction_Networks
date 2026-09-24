import proofs.SmallCusp.Classification.SourceCoverageRecordKeyIndexLemma
import proofs.SmallCusp.Classification.SourceCoverageSourceIndicesChunk00Experiment
import proofs.SmallCusp.Classification.SourceCoverageLiteralIndexKeyExperiment
import proofs.SmallCusp.Classification.SourceCoverageBatch00

namespace SmallCusp

def sourceCoverageBatch00ReducedKeysFromIndexRows : Array Nat :=
  sourceCoverageBatch00.toArray.map (fun R =>
    sourceKeyFromIndexRow
      (Array.ofFn (fun i => (R.sourceIndices i).val)))

theorem source_coverage_batch00_reduced_keys_from_index_rows_match_literals :
    sourceCoverageBatch00ReducedKeysFromIndexRows = sourceCoverageSourceKeys00 := by
  have hi : sourceCoverageBatch00IndexRows = sourceCoverageSourceIndices00 := by
    simpa [sourceCoverageBatch00IndexRowsValid] using
      source_coverage_batch00_indices_match_literals
  have hk : sourceCoverageSourceIndices00.map sourceKeyFromIndexRow =
      sourceCoverageSourceKeys00 := by
    have h := source_coverage_literal_index_keys_match
    simp only [sourceCoverageSourceIndices00KeysValid, Bool.and_eq_true] at h
    simpa using h.1
  rw [show sourceCoverageBatch00ReducedKeysFromIndexRows =
      sourceCoverageBatch00IndexRows.map sourceKeyFromIndexRow by
        simp [sourceCoverageBatch00ReducedKeysFromIndexRows,
          sourceCoverageBatch00IndexRows]]
  rw [hi]
  exact hk

end SmallCusp
