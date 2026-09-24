import proofs.SmallCusp.Classification.SourceLookupKeySetCompressed
import proofs.SmallCusp.Classification.SourceLookupSearchAllExperiment

namespace SmallCusp

theorem structuralSourceKey_has_lookup_entry
    (S : Finset BimolReactionCode)
    (hS : StructurallyEligibleSource S) :
    ∃ i : Fin sourceLookupEntries.size,
      (sourceLookupEntries[i.val]!).1 = bimolCatalogueKey S ∧
        sourceLookupSearch sourceLookupEntries 20 (bimolCatalogueKey S) 0
            sourceLookupEntries.size =
          some (sourceLookupEntries[i.val]!).2 := by
  have hcat : S ∈ structurallyEligibleSourceCatalogue := by
    simp only [structurallyEligibleSourceCatalogue, Finset.mem_filter]
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hS.1.1⟩, hS⟩
  have hkey : bimolCatalogueKey S ∈ sourceLookupKeySetCompressed := by
    rw [sourceLookupKeySetCompressed_eq_structural]
    exact Finset.mem_image.mpr ⟨S, hcat, rfl⟩
  have hkey' : bimolCatalogueKey S ∈ sourceLookupKeyListBasic :=
    List.mem_toFinset.mp hkey
  change bimolCatalogueKey S ∈ sourceLookupEntries.toList.map Prod.fst at hkey'
  rcases List.mem_map.mp hkey' with ⟨entry, hentry, heq⟩
  rcases List.mem_iff_get.mp hentry with ⟨i, hi⟩
  let i' : Fin sourceLookupEntries.size := Fin.cast (by simp) i
  have hentry' : sourceLookupEntries[i'.val]! = entry := by
    simpa [i', Array.getElem?_eq_getElem] using hi
  have hsearch := all_source_lookup_searches_self i'
  have hsearch' :
      sourceLookupSearch sourceLookupEntries 20 (bimolCatalogueKey S) 0
          sourceLookupEntries.size =
        some (sourceLookupEntries[i'.val]!).2 := by
    rw [← heq, ← hentry']
    exact hsearch
  refine ⟨i', ?_, hsearch'⟩
  rw [hentry']
  exact heq

theorem structurallyEligibleSource_lookup_some
    (S : Finset BimolReactionCode)
    (hS : StructurallyEligibleSource S) :
    ∃ entry, sourceCoverageLookup (bimolCatalogueKey S) = some entry := by
  obtain ⟨i, _, hsearch⟩ := structuralSourceKey_has_lookup_entry S hS
  refine ⟨(sourceLookupEntries[i.val]!).2, ?_⟩
  rw [sourceCoverageLookup]
  exact hsearch

end SmallCusp
