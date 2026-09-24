import proofs.SmallCusp.Classification.SourceLookupSearchSound
import proofs.SmallCusp.Classification.SourceLookupPayloadCoverage

namespace SmallCusp

theorem covers_using_lookup_some (lookup : Nat → Option (Nat × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode)
    (h : SourceLookupCoversUsing lookup records S) :
    ∃ payload, lookup (bimolCatalogueKey S) = some payload := by
  unfold SourceLookupCoversUsing at h
  cases he : lookup (bimolCatalogueKey S) with
  | none => simp only [he] at h
  | some payload => exact ⟨payload, rfl⟩

theorem source_lookup_covers_structural (S : Finset BimolReactionCode)
    (h : SourceLookupCovers S) : StructurallyEligibleSource S := by
  obtain ⟨payload, hlookup⟩ :=
    covers_using_lookup_some sourceCoverageLookup sourceCoverageArray S h
  obtain ⟨entry, hentry, hkey⟩ := source_lookup_search_key_mem
    sourceLookupEntries 20 (bimolCatalogueKey S) 0 sourceLookupEntries.size payload
    (by simpa only [sourceCoverageLookup] using hlookup)
  have hmem : bimolCatalogueKey S ∈ sourceLookupKeySetCompressed := by
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨entry, by simpa using hentry, hkey⟩
  have hstruct := sourceLookupKeySetCompressed_subset_structural hmem
  obtain ⟨T, hT, hkeyT⟩ := Finset.mem_image.mp hstruct
  have heq : T = S := bimol_catalogue_key_injective hkeyT
  subst T
  exact (Finset.mem_filter.mp hT).2

end SmallCusp
