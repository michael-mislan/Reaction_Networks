import proofs.SmallCusp.Classification.SourceLookupCore
import proofs.SmallCusp.Classification.CoverageTypes

namespace SmallCusp

set_option Elab.async false

def SourceLookupCoversUsing (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) : Prop :=
  match lookup (bimolCatalogueKey S) with
  | none => False
  | some entry =>
      match records[entry.1]? with
      | none => False
      | some R => R.Valid ∧
          (if entry.2 then codedReactionSet (swapCodedNetwork R.sourceNetwork)
            else codedReactionSet R.sourceNetwork) = S

instance sourceLookupCoversUsing_decidable (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) :
    Decidable (SourceLookupCoversUsing lookup records S) := by
  unfold SourceLookupCoversUsing
  cases hl : lookup (bimolCatalogueKey S) with
  | none => exact isFalse id
  | some entry =>
      dsimp
      cases hr : records[entry.1]? <;> infer_instance

def SourceLookupCovers (S : Finset BimolReactionCode) : Prop :=
  SourceLookupCoversUsing sourceCoverageLookup sourceCoverageArray S

instance sourceLookupCovers_decidable (S : Finset BimolReactionCode) :
    Decidable (SourceLookupCovers S) :=
  sourceLookupCoversUsing_decidable sourceCoverageLookup sourceCoverageArray S

section
variable (recordsValid : sourceCoverageRecords.all (fun R => decide R.Valid) = true)
variable (chunksChecked : ∀ P ∈ sourceLookupHead.powerset, ∀ S ∈ sourceLookupChunk P,
  StructurallyEligibleSource S ↔ SourceLookupMatches S)

private theorem array_record_valid (records : List SourceCoverageRecord)
    (valid : records.all (fun R => decide R.Valid) = true)
    {i : ℕ} {R : SourceCoverageRecord} (h : records.toArray[i]? = some R) : R.Valid := by
  have hm : R ∈ records := by
    apply List.mem_of_getElem?
    simpa using h
  have hv : ∀ R ∈ records, R.Valid := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using valid
  exact hv R hm

include recordsValid in
theorem sourceCoverageArray_valid_of_checks {i : ℕ} {R : SourceCoverageRecord}
    (h : sourceCoverageArray[i]? = some R) : R.Valid := by
  exact array_record_valid sourceCoverageRecords recordsValid
    (by simpa only [sourceCoverageArray] using h)

private theorem matchesUsing_iff_coversUsing (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord)
    (valid : ∀ (i : ℕ) (R : SourceCoverageRecord), records[i]? = some R → R.Valid) (S : Finset BimolReactionCode) :
    SourceLookupMatchesUsing lookup records S ↔ SourceLookupCoversUsing lookup records S := by
  unfold SourceLookupMatchesUsing SourceLookupCoversUsing
  cases hl : lookup (bimolCatalogueKey S) with
  | none => rfl
  | some entry =>
      dsimp
      cases hr : records[entry.1]? with
      | none => rfl
      | some R => exact ⟨fun h => ⟨valid _ _ hr, h⟩, fun h => h.2⟩

private theorem coversUsing_nonself (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode)
    (h : SourceLookupCoversUsing lookup records S) : ∀ e ∈ S, e.1 ≠ e.2 := by
  unfold SourceLookupCoversUsing at h
  cases hl : lookup (bimolCatalogueKey S) with
  | none => simp only [hl] at h
  | some entry =>
      simp only [hl] at h
      cases hr : records[entry.1]? with
      | none => simp only [hr] at h
      | some R =>
          simp only [hr] at h
          rw [← h.2]
          cases hb : entry.2
          · exact (codedReactionSet_valid R.sourceNetwork).2
          · exact (codedReactionSet_valid (swapCodedNetwork R.sourceNetwork)).2

include recordsValid in
theorem sourceLookupMatches_iff_covers_of_checks (S : Finset BimolReactionCode) :
    SourceLookupMatches S ↔ SourceLookupCovers S :=
  matchesUsing_iff_coversUsing sourceCoverageLookup sourceCoverageArray
    (fun _ _ h => sourceCoverageArray_valid_of_checks recordsValid h) S

include chunksChecked in
theorem sourceLookupMatches_iff_structural_of_checks (S : Finset BimolReactionCode)
    (hS : IsFiveReactionSourceCode S) :
    StructurallyEligibleSource S ↔ SourceLookupMatches S := by
  obtain ⟨P, hP, hSP⟩ := sourceLookupChunk_covers S hS
  exact chunksChecked P hP S hSP

include recordsValid chunksChecked in
theorem sourceCoverageLookup_complete_of_checks :
    ∀ S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5,
      StructurallyEligibleSource S → SourceLookupCovers S := by
  intro S _ hS
  exact (sourceLookupMatches_iff_covers_of_checks recordsValid S).mp
    ((sourceLookupMatches_iff_structural_of_checks chunksChecked S hS.1).mp hS)

include recordsValid chunksChecked in
theorem sourceCoverageLookup_sound_of_checks :
    ∀ S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5,
      SourceLookupCovers S → StructurallyEligibleSource S := by
  intro S hS hcover
  have hmatches := (sourceLookupMatches_iff_covers_of_checks recordsValid S).mpr hcover
  have hnonself := coversUsing_nonself sourceCoverageLookup sourceCoverageArray S hcover
  exact (sourceLookupMatches_iff_structural_of_checks chunksChecked S
    ⟨(Finset.mem_powersetCard.mp hS).2, hnonself⟩).mpr hmatches

include recordsValid chunksChecked in
theorem sourceCoverageLookup_iff_of_checks (S : Finset BimolReactionCode)
    (hS : S ∈ (Finset.univ : Finset BimolReactionCode).powersetCard 5) :
    SourceLookupCovers S ↔ StructurallyEligibleSource S :=
  ⟨sourceCoverageLookup_sound_of_checks recordsValid chunksChecked S hS, sourceCoverageLookup_complete_of_checks recordsValid chunksChecked S hS⟩

include recordsValid chunksChecked in
theorem structurallyEligibleSource_isCovered_of_checks (S : Finset BimolReactionCode)
    (hS : StructurallyEligibleSource S) : SourceLookupCovers S := by
  exact (sourceLookupMatches_iff_covers_of_checks recordsValid S).mp
    ((sourceLookupMatches_iff_structural_of_checks chunksChecked S hS.1).mp hS)

end

end SmallCusp

