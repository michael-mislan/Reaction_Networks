import proofs.RAFStructuredEnumeration.Resolution
import proofs.IrrRAFEnumeration.RestrictedCompletion

namespace RAFStructuredEnumeration
open RAF IrrRAFEnumeration

variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

/-- Deleting reaction identifiers filters the original complete minimal family.
The right side is restricted minimality with original identifiers; restrict_isRAF
identifies this with the existing subtype CRS representation. -/
theorem catalogue_restriction (Q : CRS M R) (cats : R → Finset M) (U I : Finset R) :
    I ∈ (supplierCatalogue Q cats).filter (fun J => J ⊆ U) ↔
      Minimal (fun S => S ⊆ U ∧ IsRAF Q (fun x r => x ∈ cats r) S) I := by
  classical
  rw [Finset.mem_filter, supplierCatalogue_correct, minimal_within_iff]
  rfl

theorem catalogue_restriction_family (Q : CRS M R) (cats : R → Finset M) (U : Finset R) :
    (supplierCatalogue Q cats).filter (fun J => J ⊆ U) =
      familyWithin Q (fun x r => x ∈ cats r) U := by
  classical
  ext I
  rw [catalogue_restriction, mem_familyWithin]

end RAFStructuredEnumeration
