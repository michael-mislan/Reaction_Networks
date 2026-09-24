import proofs.SmallCusp.Classification.SourceLookupPayloadIdentity
import proofs.SmallCusp.Classification.SourceLookupSound
import proofs.SmallCusp.Classification.SourceCoverage

namespace SmallCusp

theorem structurallyEligibleSource_isCovered (S : Finset BimolReactionCode)
    (hS : StructurallyEligibleSource S) : SourceLookupCovers S :=
  structurallyEligibleSource_covered_of_payload_identity sourceCoverageRecords_valid
    (source_lookup_payload_identity sourceCoverageRecords_valid) S hS

theorem sourceCoverageLookup_complete :
    ∀ S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5,
      StructurallyEligibleSource S → SourceLookupCovers S := by
  intro S _ hS
  exact structurallyEligibleSource_isCovered S hS

theorem sourceCoverageLookup_sound :
    ∀ S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5,
      SourceLookupCovers S → StructurallyEligibleSource S := by
  intro S _ hS
  exact source_lookup_covers_structural S hS

theorem sourceCoverageLookup_iff (S : Finset BimolReactionCode)
    (hS : S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5) :
    SourceLookupCovers S ↔ StructurallyEligibleSource S :=
  ⟨sourceCoverageLookup_sound S hS, sourceCoverageLookup_complete S hS⟩

end SmallCusp
