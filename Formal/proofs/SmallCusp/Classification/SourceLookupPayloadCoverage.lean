import proofs.SmallCusp.Classification.SourceLookupKeySetSearchBridge
import proofs.SmallCusp.Classification.SourceLookupBridge
import proofs.SmallCusp.Classification.BimolCatalogueKeyInjective

namespace SmallCusp

theorem source_lookup_matches_using_of_key_identity
    (lookup : Nat → Option (Nat × Bool)) (records : Array SourceCoverageRecord)
    (entry : Nat × Nat × Bool) (R : SourceCoverageRecord)
    (S : Finset BimolReactionCode)
    (hlookup : lookup (bimolCatalogueKey S) = some entry.2)
    (hactual : records[entry.2.1]? = some R)
    (hkey : bimolCatalogueKey
      (if entry.2.2 then codedReactionSet (swapCodedNetwork R.sourceNetwork)
       else codedReactionSet R.sourceNetwork) = bimolCatalogueKey S) :
    SourceLookupMatchesUsing lookup records S := by
  have heq := bimol_catalogue_key_injective hkey
  unfold SourceLookupMatchesUsing
  rw [hlookup]
  change (match records[entry.2.1]? with
    | none => False
    | some R₁ => (if entry.2.2 then
        codedReactionSet (swapCodedNetwork R₁.sourceNetwork)
      else codedReactionSet R₁.sourceNetwork) = S)
  rw [hactual]
  exact heq

/-- Exact all-row payload obligation; validity is supplied independently. -/
def SourceLookupPayloadIdentity : Prop :=
  ∀ i : Fin sourceLookupEntries.size, ∃ R : SourceCoverageRecord,
    sourceCoverageArray[(sourceLookupEntries[i.val]!).2.1]? = some R ∧
    bimolCatalogueKey
      (if (sourceLookupEntries[i.val]!).2.2 then
        codedReactionSet (swapCodedNetwork R.sourceNetwork)
      else codedReactionSet R.sourceNetwork) = (sourceLookupEntries[i.val]!).1

theorem structurallyEligibleSource_matches_of_payload_identity
    (identity : SourceLookupPayloadIdentity)
    (S : Finset BimolReactionCode) (hS : StructurallyEligibleSource S) :
    SourceLookupMatches S := by
  obtain ⟨i, hkey, hsearch⟩ := structuralSourceKey_has_lookup_entry S hS
  obtain ⟨R, hactual, hrecordkey⟩ := identity i
  exact source_lookup_matches_using_of_key_identity sourceCoverageLookup
    sourceCoverageArray (sourceLookupEntries[i.val]!) R S
    (by simpa only [sourceCoverageLookup] using hsearch)
    hactual (hrecordkey.trans hkey)

theorem structurallyEligibleSource_covered_of_payload_identity
    (recordsValid : sourceCoverageRecords.all (fun R => decide R.Valid) = true)
    (identity : SourceLookupPayloadIdentity)
    (S : Finset BimolReactionCode) (hS : StructurallyEligibleSource S) :
    SourceLookupCovers S :=
  (sourceLookupMatches_iff_covers_of_checks recordsValid S).mp
    (structurallyEligibleSource_matches_of_payload_identity identity S hS)

end SmallCusp
