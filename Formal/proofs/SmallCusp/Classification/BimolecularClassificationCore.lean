import proofs.SmallCusp.Classification.SourceLookupBridge

namespace SmallCusp

def SourceLookupCuspUsing (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) : Prop :=
  match lookup (bimolCatalogueKey S) with
  | none => False
  | some entry =>
      match records[entry.1]? with
      | none => False
      | some R => R.Valid ∧
          (if entry.2 then codedReactionSet (swapCodedNetwork R.sourceNetwork)
            else codedReactionSet R.sourceNetwork) = S ∧
          R.outcome = .cusp

instance sourceLookupCuspUsing_decidable (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) :
    Decidable (SourceLookupCuspUsing lookup records S) := by
  unfold SourceLookupCuspUsing
  cases hl : lookup (bimolCatalogueKey S) with
  | none => exact isFalse id
  | some entry =>
      dsimp
      cases hr : records[entry.1]? <;> infer_instance

def SourceLookupCusp (S : Finset BimolReactionCode) : Prop :=
  SourceLookupCuspUsing sourceCoverageLookup sourceCoverageArray S

instance sourceLookupCusp_decidable (S : Finset BimolReactionCode) :
    Decidable (SourceLookupCusp S) :=
  sourceLookupCuspUsing_decidable sourceCoverageLookup sourceCoverageArray S

private theorem record_source_cusp_iff_oriented
    (R : SourceCoverageRecord) (swapSource : Bool) :
    AdmitsTransverseCusp R.sourceNetwork.toNetwork ↔
      AdmitsTransverseCusp
        (if swapSource then swapCodedNetwork R.sourceNetwork else R.sourceNetwork).toNetwork := by
  cases swapSource
  · simp
  · simpa using (swapCodedNetwork_admitsTransverseCusp_iff R.sourceNetwork).symm

private theorem cuspUsing_admits (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (C : CodedBimolNetwork)
    (h : SourceLookupCuspUsing lookup records (codedReactionSet C)) :
    AdmitsTransverseCusp C.toNetwork := by
  unfold SourceLookupCuspUsing at h
  cases hl : lookup (bimolCatalogueKey (codedReactionSet C)) with
  | none => simp only [hl] at h
  | some entry =>
    simp only [hl] at h
    cases hr : records[entry.1]? with
    | none => simp only [hr] at h
    | some R =>
      simp only [hr] at h
      rcases h with ⟨hvalid, hset, hout⟩
      have hsource : AdmitsTransverseCusp R.sourceNetwork.toNetwork :=
        (R.classifies hvalid).mpr hout
      have horiented : AdmitsTransverseCusp
          (if entry.2 then swapCodedNetwork R.sourceNetwork else R.sourceNetwork).toNetwork :=
        (record_source_cusp_iff_oriented R entry.2).mp hsource
      exact (codedReactionSet_eq_cusp_iff C
        (if entry.2 then swapCodedNetwork R.sourceNetwork else R.sourceNetwork)
        (by simpa only [apply_ite] using hset.symm)).mpr horiented

private theorem cuspUsing_of_covered (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (C : CodedBimolNetwork)
    (hcusp : AdmitsTransverseCusp C.toNetwork)
    (hcovered : SourceLookupCoversUsing lookup records (codedReactionSet C)) :
    SourceLookupCuspUsing lookup records (codedReactionSet C) := by
  unfold SourceLookupCoversUsing at hcovered
  unfold SourceLookupCuspUsing
  cases hl : lookup (bimolCatalogueKey (codedReactionSet C)) with
  | none => simp only [hl] at hcovered
  | some entry =>
    simp only [hl] at hcovered ⊢
    cases hr : records[entry.1]? with
    | none => simp only [hr] at hcovered
    | some R =>
      simp only [hr] at hcovered ⊢
      rcases hcovered with ⟨hvalid, hset⟩
      refine ⟨hvalid, hset, ?_⟩
      have horiented : AdmitsTransverseCusp
          (if entry.2 then swapCodedNetwork R.sourceNetwork else R.sourceNetwork).toNetwork :=
        (codedReactionSet_eq_cusp_iff C
          (if entry.2 then swapCodedNetwork R.sourceNetwork else R.sourceNetwork)
          (by simpa only [apply_ite] using hset.symm)).mp hcusp
      have hsource : AdmitsTransverseCusp R.sourceNetwork.toNetwork :=
        (record_source_cusp_iff_oriented R entry.2).mpr horiented
      exact (R.classifies hvalid).mp hsource

theorem sourceLookupCusp_admits (C : CodedBimolNetwork)
    (h : SourceLookupCusp (codedReactionSet C)) : AdmitsTransverseCusp C.toNetwork :=
  cuspUsing_admits sourceCoverageLookup sourceCoverageArray C h

theorem sourceLookupCusp_of_cusp_of_covered (C : CodedBimolNetwork)
    (hcusp : AdmitsTransverseCusp C.toNetwork)
    (hcovered : SourceLookupCovers (codedReactionSet C)) :
    SourceLookupCusp (codedReactionSet C) :=
  cuspUsing_of_covered sourceCoverageLookup sourceCoverageArray C hcusp hcovered

/-- Source-faithful membership in the 52 positive simple-equivalence classes.
The witness is an exact bimolecular encoding of the literal network, and the
lookup certificate includes both its generator-set equality and its positive
class tag. -/
def BelongsToBimolecularCuspClass (Q : SmallPlanarNetwork 5) : Prop :=
  ∃ C : CodedBimolNetwork,
    C.toNetwork = Q ∧ SourceLookupCusp (codedReactionSet C)

/-- Membership in one of the 52 positive source classes supplies a literal
transverse-cusp witness. -/
theorem cusp_if_in_52 (Q : SmallPlanarNetwork 5)
    (hclass : BelongsToBimolecularCuspClass Q) :
    AdmitsTransverseCusp Q := by
  rcases hclass with ⟨C, hnet, hlookup⟩
  rw [← hnet]
  exact sourceLookupCusp_admits C hlookup

/-- A literal planar bimolecular `(2,5,2)` source outside the 52 positive
classes cannot admit a transverse cusp. -/
theorem no_cusp_if_not_in_52_of_coverage
    (coverage : ∀ S, StructurallyEligibleSource S → SourceLookupCovers S) (Q : SmallPlanarNetwork 5)
    (hQ : IsPlanarBimolecular252 Q)
    (hnot : ¬ BelongsToBimolecularCuspClass Q) :
    ¬ AdmitsTransverseCusp Q := by
  intro hcusp
  apply hnot
  let C := encodeBimolNetwork Q hQ.1 hQ.2.1
  have hnet : C.toNetwork = Q := encodeBimolNetwork_toNetwork Q hQ.1 hQ.2.1
  have hstruct : StructurallyEligibleSource (codedReactionSet C) :=
    cusp_source_structurallyEligible Q hQ hcusp
  have hcovered := coverage _ hstruct
  have hcoded : AdmitsTransverseCusp C.toNetwork := by simpa [hnet] using hcusp
  exact ⟨C, hnet, sourceLookupCusp_of_cusp_of_covered C hcoded hcovered⟩

/-- Literal planar bimolecular `(2,5,2)` cusp classification. -/
theorem classify_planar_bimolecular_2_5_2_cusps_of_coverage
    (coverage : ∀ S, StructurallyEligibleSource S → SourceLookupCovers S)
    (Q : SmallPlanarNetwork 5) (hQ : IsPlanarBimolecular252 Q) :
    AdmitsTransverseCusp Q ↔ BelongsToBimolecularCuspClass Q := by
  constructor
  · intro hcusp
    by_contra hnot
    exact no_cusp_if_not_in_52_of_coverage coverage Q hQ hnot hcusp
  · exact cusp_if_in_52 Q

end SmallCusp
