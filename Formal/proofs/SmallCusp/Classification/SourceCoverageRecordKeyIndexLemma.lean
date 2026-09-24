import proofs.SmallCusp.Classification.SourceCoverageRecordKeyReducedLemma
import proofs.SmallCusp.Classification.SourceCoverageLiteralIndexKeyExperiment

namespace SmallCusp

def sourceKeyFromIndexFin (f : Fin 5 → Fin 30) : Nat :=
  ∑ r : Fin 5, sourceBitWeight (f r)

def sourceSwappedKeyFromIndexFin (f : Fin 5 → Fin 30) : Nat :=
  ∑ r : Fin 5, sourceSwappedBitWeight (f r)

theorem source_coverage_record_reduced_key_eq_index_fin
    (R : SourceCoverageRecord) :
    sourceCoverageRecordReducedKey R = sourceKeyFromIndexFin R.sourceIndices := by
  simp [sourceCoverageRecordReducedKey, sourceKeyFromIndexFin, source_bit_weight_eq]

theorem source_key_from_index_row_ofFn
    (f : Fin 5 → Fin 30) :
    sourceKeyFromIndexRow (Array.ofFn (fun i => (f i).val)) =
      sourceKeyFromIndexFin f := by
  simp [sourceKeyFromIndexRow, sourceKeyFromIndexFin, sourceBitWeight,
    Fin.sum_univ_succ]

theorem source_coverage_record_reduced_key_eq_index_row
    (R : SourceCoverageRecord) :
    sourceCoverageRecordReducedKey R =
      sourceKeyFromIndexRow
        (Array.ofFn (fun i => (R.sourceIndices i).val)) := by
  rw [source_coverage_record_reduced_key_eq_index_fin,
    source_key_from_index_row_ofFn]

theorem source_coverage_record_reduced_swapped_key_eq_index_fin
    (R : SourceCoverageRecord) :
    sourceCoverageRecordReducedSwappedKey R =
      sourceSwappedKeyFromIndexFin R.sourceIndices := by
  simp [sourceCoverageRecordReducedSwappedKey, sourceSwappedKeyFromIndexFin,
    source_swapped_bit_weight_eq]

theorem source_swapped_key_from_index_row_ofFn
    (f : Fin 5 → Fin 30) :
    sourceSwappedKeyFromIndexRow (Array.ofFn (fun i => (f i).val)) =
      sourceSwappedKeyFromIndexFin f := by
  simp [sourceSwappedKeyFromIndexRow, sourceSwappedKeyFromIndexFin,
    sourceSwappedBitWeight, Fin.sum_univ_succ]

theorem source_coverage_record_reduced_swapped_key_eq_index_row
    (R : SourceCoverageRecord) :
    sourceCoverageRecordReducedSwappedKey R =
      sourceSwappedKeyFromIndexRow
        (Array.ofFn (fun i => (R.sourceIndices i).val)) := by
  rw [source_coverage_record_reduced_swapped_key_eq_index_fin,
    source_swapped_key_from_index_row_ofFn]

end SmallCusp
