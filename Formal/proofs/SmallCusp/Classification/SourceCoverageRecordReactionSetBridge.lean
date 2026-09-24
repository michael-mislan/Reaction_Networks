import proofs.SmallCusp.Classification.SourceCoverageArrayBatch00KeyPrefix
import proofs.SmallCusp.Classification.StructuralSources

namespace SmallCusp

theorem source_coverage_record_reaction_set_eq_coded_source_network
    (R : SourceCoverageRecord) (h : Function.Injective R.sourceIndices) :
    sourceCoverageRecordReactionSet R = codedReactionSet R.sourceNetwork := by
  ext e
  simp only [sourceCoverageRecordReactionSet, codedReactionSet,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, by simp [SourceCoverageRecord.sourceNetwork, h]⟩
  · rintro ⟨r, hr⟩
    exact ⟨r, by simpa [SourceCoverageRecord.sourceNetwork, h] using hr⟩

theorem source_coverage_record_swapped_reaction_set_eq_coded_source_network
    (R : SourceCoverageRecord) (h : Function.Injective R.sourceIndices) :
    swapBimolReactionSet (sourceCoverageRecordReactionSet R) =
      codedReactionSet (swapCodedNetwork R.sourceNetwork) := by
  ext e
  simp only [sourceCoverageRecordReactionSet, swapBimolReactionSet,
    codedReactionSet, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨e', ⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp [swapCodedNetwork, SourceCoverageRecord.sourceNetwork, h]⟩
  · rintro ⟨r, rfl⟩
    refine ⟨bimolReactionCatalogue (R.sourceIndices r),
      ⟨r, rfl⟩, ?_⟩
    simp [swapCodedNetwork, SourceCoverageRecord.sourceNetwork, h]

end SmallCusp
