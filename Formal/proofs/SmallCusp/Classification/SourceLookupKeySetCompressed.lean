import proofs.SmallCusp.Classification.SourceLookupDecodedMembershipFullExperiment
import proofs.SmallCusp.Classification.SourceLookupKeyBasicExperiment
import proofs.SmallCusp.Classification.SourceCatalogueCount
import proofs.SmallCusp.Classification.BimolCatalogueKeyInjective

namespace SmallCusp

def sourceLookupKeySetCompressed : Finset Nat :=
  sourceLookupKeyListBasic.toFinset

def structuralSourceKeySetCompressed : Finset Nat :=
  structurallyEligibleSourceCatalogue.image bimolCatalogueKey

theorem sourceLookupKeySetCompressed_subset_structural :
    sourceLookupKeySetCompressed ⊆ structuralSourceKeySetCompressed := by
  intro key hkey
  have hkey' : key ∈ sourceLookupKeyListBasic :=
    List.mem_toFinset.mp hkey
  change key ∈ sourceLookupEntries.toList.map Prod.fst at hkey'
  rcases List.mem_map.mp hkey' with ⟨entry, hentry, heq⟩
  subst key
  rcases List.mem_iff_get.mp hentry with ⟨i, hi⟩
  let i' : Fin sourceLookupEntries.size := Fin.cast (by simp) i
  have hd := all_decoded_lookup_entries_structural i'
  dsimp at hd
  have hentry' : sourceLookupEntries[i'.val]! = entry := by
    simpa [i', Array.getElem?_eq_getElem] using hi
  rw [hentry'] at hd
  have hcat : reactionSetAtKeyFull entry.1 ∈
      structurallyEligibleSourceCatalogue := by
    simp only [structurallyEligibleSourceCatalogue, Finset.mem_filter]
    exact ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, hd.1.1.1⟩, hd.1⟩
  exact Finset.mem_image.mpr ⟨reactionSetAtKeyFull entry.1, hcat, hd.2⟩

theorem structuralSourceKeySetCompressed_card :
    structuralSourceKeySetCompressed.card = 60036 := by
  rw [structuralSourceKeySetCompressed,
    Finset.card_image_of_injective _ bimol_catalogue_key_injective]
  exact structurallyEligibleSourceCatalogue_card

theorem sourceLookupKeySetCompressed_card :
    sourceLookupKeySetCompressed.card = 60036 := by
  rw [sourceLookupKeySetCompressed,
    List.toFinset_card_of_nodup sourceLookupKeyList_nodup_basic]
  simpa [sourceLookupKeyListBasic] using sourceLookupEntries_size_basic

theorem sourceLookupKeySetCompressed_eq_structural :
    sourceLookupKeySetCompressed = structuralSourceKeySetCompressed := by
  apply Finset.eq_of_subset_of_card_le sourceLookupKeySetCompressed_subset_structural
  rw [structuralSourceKeySetCompressed_card, sourceLookupKeySetCompressed_card]

end SmallCusp
