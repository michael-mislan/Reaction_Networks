import proofs.SmallCusp.Classification.LightCoverageTypes
import proofs.SmallCusp.Classification.SourceKeyImageLemmaExperiment

namespace SmallCusp

def sourceCoverageRecordReducedKey (R : SourceCoverageRecord) : Nat :=
  ∑ r : Fin 5,
    2 ^ bimolReactionIndex (bimolReactionCatalogue (R.sourceIndices r))

def sourceCoverageRecordReducedSwappedKey (R : SourceCoverageRecord) : Nat :=
  ∑ r : Fin 5,
    2 ^ bimolReactionIndex
      (swapBimolReaction (bimolReactionCatalogue (R.sourceIndices r)))

theorem bimol_catalogue_key_swap_univ_image
    (f : Fin 5 → BimolReactionCode) (hf : Function.Injective f) :
    bimolCatalogueKey
        (swapBimolReactionSet (Finset.univ.image f)) =
      ∑ r : Fin 5, 2 ^ bimolReactionIndex (swapBimolReaction (f r)) := by
  rw [swapBimolReactionSet, Finset.image_image]
  exact bimol_catalogue_key_univ_image
    (fun r => swapBimolReaction (f r))
    (by
      intro a b hab
      exact hf (swapBimolReaction_injective hab))

theorem source_coverage_record_key_eq_reduced
    (R : SourceCoverageRecord) (h : Function.Injective R.sourceIndices) :
    bimolCatalogueKey
    (Finset.univ.image (fun r => bimolReactionCatalogue (R.sourceIndices r))) =
      sourceCoverageRecordReducedKey R := by
  simpa [sourceCoverageRecordReducedKey] using
    (bimol_catalogue_key_univ_image
      (fun r => bimolReactionCatalogue (R.sourceIndices r))
      (by
        intro a b hab
        exact h (bimolReactionCatalogue_injective hab)))

theorem source_coverage_record_swapped_key_eq_reduced
    (R : SourceCoverageRecord) (h : Function.Injective R.sourceIndices) :
    bimolCatalogueKey
        (swapBimolReactionSet
    (Finset.univ.image
            (fun r => bimolReactionCatalogue (R.sourceIndices r)))) =
      sourceCoverageRecordReducedSwappedKey R := by
  simpa [sourceCoverageRecordReducedSwappedKey] using
    (bimol_catalogue_key_swap_univ_image
      (fun r => bimolReactionCatalogue (R.sourceIndices r))
      (by
        intro a b hab
        exact h (bimolReactionCatalogue_injective hab)))

end SmallCusp
