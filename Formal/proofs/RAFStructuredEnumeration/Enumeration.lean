import proofs.RAFStructuredEnumeration.CandidateCoverage
import proofs.RAFStructuredEnumeration.Cost

namespace RAFStructuredEnumeration
open RAF RAF.Frankl RAFQueryCompilation MinRAFApprox.SetCoverSource
variable {M R : Type*} [DecidableEq M] [DecidableEq R] [LinearOrder M]
  [Fintype M] [Fintype R]

def originalMax (Q : CRS M R) (cats : R → Finset M) : Finset R :=
  evaluate Q (fun x r => x ∈ cats r) Finset.univ

noncomputable def allCandidates (Q : CRS M R) (cats : R → Finset M) : Finset (Finset R) :=
  (resolutions Q cats (originalMax Q cats)).biUnion
    (fun pc => resolutionCandidates Q (originalMax Q cats) pc.1 pc.2)

noncomputable def supplierCatalogue (Q : CRS M R) (cats : R → Finset M) : Finset (Finset R) := by
  classical
  exact (allCandidates Q cats).filter (IsIrreducibleRAF Q (fun x r => x ∈ cats r))

theorem supplierCatalogue_correct (Q : CRS M R) (cats : R → Finset M) (I : Finset R) :
    I ∈ supplierCatalogue Q cats ↔ IsIrreducibleRAF Q (fun x r => x ∈ cats r) I := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨?_, h⟩
    obtain ⟨p,c,hpc,hcand⟩ := original_irr_candidate Q cats (originalMax Q cats) I
      (raf_subset_evaluate Q (fun x r => x ∈ cats r) (Finset.subset_univ I) h.1)
      (fixed_supported _ _ (evaluate_fixed _ _ Finset.univ)) h
    exact Finset.mem_biUnion.mpr ⟨(p,c), hpc, hcand⟩

theorem allCandidates_card (Q : CRS M R) (cats : R → Finset M) :
    (allCandidates Q cats).card ≤ (originalMax Q cats).card *
      (resolutions Q cats (originalMax Q cats)).card := by
  classical
  calc
    (allCandidates Q cats).card ≤
        ∑ pc ∈ resolutions Q cats (originalMax Q cats),
          (resolutionCandidates Q (originalMax Q cats) pc.1 pc.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _pc ∈ resolutions Q cats (originalMax Q cats), (originalMax Q cats).card :=
      Finset.sum_le_sum (fun pc _ => resolutionCandidates_card Q _ pc.1 pc.2)
    _ = _ := by simp [Nat.mul_comm]

theorem supplierCatalogue_card (Q : CRS M R) (cats : R → Finset M) :
    (supplierCatalogue Q cats).card ≤ (originalMax Q cats).card *
      2^(supplierExcess Q cats (originalMax Q cats)) := by
  classical
  calc
    (supplierCatalogue Q cats).card ≤ (allCandidates Q cats).card := Finset.card_filter_le _ _
    _ ≤ (originalMax Q cats).card * (resolutions Q cats (originalMax Q cats)).card :=
      allCandidates_card Q cats
    _ ≤ _ := Nat.mul_le_mul_left _ (resolutions_excess_bound Q cats _
      (fixed_supported _ _ (evaluate_fixed _ _ Finset.univ)))

end RAFStructuredEnumeration
