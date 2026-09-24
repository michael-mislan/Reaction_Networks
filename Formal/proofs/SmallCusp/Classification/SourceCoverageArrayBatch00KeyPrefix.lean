import proofs.SmallCusp.Classification.BimolCatalogueKeyInjective
import proofs.SmallCusp.Classification.SourceCoverageArrayBatch00Prefix
import proofs.SmallCusp.Classification.SourceCoverageBatch00ComputedKeyBridge
import proofs.SmallCusp.Classification.SourceCoverageBatch00ComputedSwappedKeyBridge

namespace SmallCusp

def sourceCoverageRecordReactionSet (R : SourceCoverageRecord) :
    Finset BimolReactionCode :=
  Finset.univ.image (fun r => bimolReactionCatalogue (R.sourceIndices r))

theorem source_coverage_array_batch00_canonical_key_prefix
    (j : Fin 500) {R : SourceCoverageRecord}
    (hR : sourceCoverageArray[j.val]? = some R) :
    bimolCatalogueKey
        (sourceCoverageRecordReactionSet R) =
      sourceCoverageSourceKeys00[j.val]! := by
  have hrec := source_coverage_array_batch00_prefix j
  have hbatch : sourceCoverageBatch00.toArray[j.val]? = some R :=
    hrec.symm.trans hR
  have hkeys := congrArg (fun a : Array Nat => a[j.val]!)
    source_coverage_batch00_computed_keys_match_literals
  cases hget : sourceCoverageBatch00.toArray[j.val]? with
  | none => simp [hget] at hbatch
  | some R₀ =>
      have hR₀ : R₀ = R := Option.some.inj (by simpa [hget] using hbatch)
      subst R
      have hkeys' := hkeys
      simp only [sourceCoverageBatch00ComputedKeys] at hkeys'
      have hidx : j.val < sourceCoverageBatch00.toArray.size := by
        simp [sourceCoverageBatch00_length]
      have hv : sourceCoverageBatch00.toArray[j.val]'hidx = R₀ := by
        apply Option.some.inj
        simpa only [getElem?_pos, hidx, Option.some.injEq] using hget
      have hmap :
          (sourceCoverageBatch00.toArray.map (fun R =>
            bimolCatalogueKey
              (Finset.univ.image (fun r => bimolReactionCatalogue (R.sourceIndices r)))))[j.val]! =
            bimolCatalogueKey
              (Finset.univ.image (fun r => bimolReactionCatalogue (R₀.sourceIndices r))) := by
        simp only [getElem!_pos, hidx, Array.getElem_map, Array.size_map]
        rw [hv]
      rw [hmap] at hkeys'
      exact hkeys'

theorem source_coverage_array_batch00_swapped_key_prefix
    (j : Fin 500) {R : SourceCoverageRecord}
    (hR : sourceCoverageArray[j.val]? = some R) :
    bimolCatalogueKey
        (swapBimolReactionSet
          (sourceCoverageRecordReactionSet R)) =
      sourceCoverageSourceKeysSwapped00[j.val]! := by
  have hrec := source_coverage_array_batch00_prefix j
  have hbatch : sourceCoverageBatch00.toArray[j.val]? = some R :=
    hrec.symm.trans hR
  have hkeys := congrArg (fun a : Array Nat => a[j.val]!)
    source_coverage_batch00_computed_swapped_keys_match_literals
  cases hget : sourceCoverageBatch00.toArray[j.val]? with
  | none => simp [hget] at hbatch
  | some R₀ =>
      have hR₀ : R₀ = R := Option.some.inj (by simpa [hget] using hbatch)
      subst R
      have hkeys' := hkeys
      simp only [sourceCoverageBatch00ComputedSwappedKeys] at hkeys'
      have hidx : j.val < sourceCoverageBatch00.toArray.size := by
        simp [sourceCoverageBatch00_length]
      have hv : sourceCoverageBatch00.toArray[j.val]'hidx = R₀ := by
        apply Option.some.inj
        simpa only [getElem?_pos, hidx, Option.some.injEq] using hget
      have hmap :
          (sourceCoverageBatch00.toArray.map (fun R =>
            bimolCatalogueKey
              (swapBimolReactionSet
                (Finset.univ.image (fun r => bimolReactionCatalogue (R.sourceIndices r))))))[j.val]! =
            bimolCatalogueKey
              (swapBimolReactionSet
                (Finset.univ.image (fun r => bimolReactionCatalogue (R₀.sourceIndices r)))) := by
        simp only [getElem!_pos, hidx, Array.getElem_map, Array.size_map]
        rw [hv]
      rw [hmap] at hkeys'
      exact hkeys'

end SmallCusp
