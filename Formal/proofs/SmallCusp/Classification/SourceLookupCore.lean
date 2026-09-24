import proofs.SmallCusp.Classification.SourceCoverageSources
import proofs.SmallCusp.Classification.StructuralSources
import proofs.SmallCusp.Classification.SourceLookupTable

namespace SmallCusp


def sourceLookupSearch (entries : Array (ℕ × ℕ × Bool)) : ℕ → ℕ → ℕ → ℕ → Option (ℕ × Bool)
  | 0, _, _, _ => none
  | fuel+1, key, lo, hi =>
      if lo < hi then
        let mid := (lo+hi)/2
        match entries[mid]? with
        | none => none
        | some entry =>
          if key = entry.1 then some entry.2
          else if key < entry.1 then sourceLookupSearch entries fuel key lo mid
          else sourceLookupSearch entries fuel key (mid+1) hi
      else none


@[irreducible] def sourceCoverageLookup (key : ℕ) : Option (ℕ × Bool) :=
  sourceLookupSearch sourceLookupEntries 20 key 0 sourceLookupEntries.size


/-- Source identity only. Record validity is inherited from its aggregate theorem. -/
def SourceLookupMatchesUsing (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) : Prop :=
  match lookup (bimolCatalogueKey S) with
  | none => False
  | some entry =>
      match records[entry.1]? with
      | none => False
      | some R =>
          (if entry.2 then codedReactionSet (swapCodedNetwork R.sourceNetwork)
            else codedReactionSet R.sourceNetwork) = S


instance sourceLookupMatchesUsing_decidable (lookup : ℕ → Option (ℕ × Bool))
    (records : Array SourceCoverageRecord) (S : Finset BimolReactionCode) :
    Decidable (SourceLookupMatchesUsing lookup records S) := by
  unfold SourceLookupMatchesUsing
  cases hl : lookup (bimolCatalogueKey S) with
  | none => exact isFalse id
  | some entry =>
      dsimp
      cases hr : records[entry.1]? <;> infer_instance

def SourceLookupMatches (S : Finset BimolReactionCode) : Prop :=
  SourceLookupMatchesUsing sourceCoverageLookup sourceCoverageArray S

instance sourceLookupMatches_decidable (S : Finset BimolReactionCode) :
    Decidable (SourceLookupMatches S) :=
  sourceLookupMatchesUsing_decidable sourceCoverageLookup sourceCoverageArray S


def sourceLookupUniverse : Finset BimolReactionCode :=
  (Finset.univ : Finset BimolReactionCode).filter (fun e => e.1 ≠ e.2)

def sourceLookupHead : Finset BimolReactionCode :=
  {(.zero,.x), (.zero,.y), (.zero,.xx), (.zero,.xy), (.zero,.yy), (.x,.zero)}

def sourceLookupChunk (P : Finset BimolReactionCode) : Finset (Finset BimolReactionCode) :=
  ((sourceLookupUniverse \ sourceLookupHead).powersetCard (5-P.card)).image (fun T => P ∪ T)

theorem sourceLookupChunk_covers (S : Finset BimolReactionCode)
    (hS : IsFiveReactionSourceCode S) :
    ∃ P ∈ sourceLookupHead.powerset, S ∈ sourceLookupChunk P := by
  classical
  refine ⟨S ∩ sourceLookupHead, Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨S \ sourceLookupHead, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
  · intro e he
    have hmem := Finset.mem_sdiff.mp he
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hS.2 e hmem.1⟩, hmem.2⟩
  · have hc := Finset.card_sdiff_add_card_inter S sourceLookupHead
    have hcard := hS.1
    omega
  · ext e
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto

end SmallCusp
