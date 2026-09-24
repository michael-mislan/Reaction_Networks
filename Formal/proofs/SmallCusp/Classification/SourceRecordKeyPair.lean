import proofs.SmallCusp.Classification.SourceCoverageRecordKeyIndexLemma
import proofs.SmallCusp.Classification.SourceCoverageRecordReactionSetBridge

namespace SmallCusp

def sourceRecordKeyPair (R : SourceCoverageRecord) : Nat × Nat :=
  (sourceKeyFromIndexRow (Array.ofFn (fun i => (R.sourceIndices i).val)),
   sourceSwappedKeyFromIndexRow (Array.ofFn (fun i => (R.sourceIndices i).val)))

theorem source_record_key_pair_canonical (R : SourceCoverageRecord)
    (h : R.Docked) :
    (sourceRecordKeyPair R).1 = bimolCatalogueKey (codedReactionSet R.sourceNetwork) := by
  rw [← source_coverage_record_reaction_set_eq_coded_source_network R h.1]
  exact (source_coverage_record_key_eq_reduced R h.1).trans
    (source_coverage_record_reduced_key_eq_index_row R) |>.symm

theorem source_record_key_pair_swapped (R : SourceCoverageRecord)
    (h : R.Docked) :
    (sourceRecordKeyPair R).2 =
      bimolCatalogueKey (codedReactionSet (swapCodedNetwork R.sourceNetwork)) := by
  rw [← source_coverage_record_swapped_reaction_set_eq_coded_source_network R h.1]
  exact (source_coverage_record_swapped_key_eq_reduced R h.1).trans
    (source_coverage_record_reduced_swapped_key_eq_index_row R) |>.symm

end SmallCusp
