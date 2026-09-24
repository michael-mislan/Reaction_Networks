import proofs.RAFStructuredEnumeration.Enumeration

namespace RAFStructuredEnumeration
open RAF MinRAFApprox.SetCoverSource

/-- Complete original-model family equality and the explicit supplier-excess bound.
The input supplies only the finite ordinary CRS and its catalyst lists. -/
theorem supplierEnumeration_correct {M R : Type*} [DecidableEq M] [DecidableEq R]
    [LinearOrder M] [Fintype M] [Fintype R] (Q : CRS M R) (cats : R → Finset M) :
    (∀ I, I ∈ supplierCatalogue Q cats ↔ IsIrreducibleRAF Q (fun x r => x ∈ cats r) I) ∧
    (allCandidates Q cats).card ≤ (originalMax Q cats).card *
      (resolutions Q cats (originalMax Q cats)).card ∧
    (resolutions Q cats (originalMax Q cats)).card ≤
      2^(supplierExcess Q cats (originalMax Q cats)) ∧
    (supplierCatalogue Q cats).card ≤ (originalMax Q cats).card *
      2^(supplierExcess Q cats (originalMax Q cats)) := by
  exact ⟨supplierCatalogue_correct Q cats, allCandidates_card Q cats,
    resolutions_excess_bound Q cats _
      (RAFQueryCompilation.fixed_supported _ _
        (RAFQueryCompilation.evaluate_fixed _ _ Finset.univ)), supplierCatalogue_card Q cats⟩

end RAFStructuredEnumeration
