import proofs.SmallCusp.Classification.SourceLookupCore

namespace SmallCusp

def reactionPresentAtKeyFull (key : Nat) (e : BimolReactionCode) : Prop :=
  (key / 2 ^ bimolReactionIndex e) % 2 = 1

instance reactionPresentAtKeyFull_decidable (key : Nat) :
    DecidablePred (reactionPresentAtKeyFull key) := by
  intro e
  unfold reactionPresentAtKeyFull
  infer_instance

def reactionSetAtKeyFull (key : Nat) : Finset BimolReactionCode :=
  Finset.univ.filter (reactionPresentAtKeyFull key)

theorem all_decoded_lookup_entries_structural :
    ∀ i : Fin sourceLookupEntries.size,
      let entry := sourceLookupEntries[i.val]!
      StructurallyEligibleSource (reactionSetAtKeyFull entry.1) ∧
        bimolCatalogueKey (reactionSetAtKeyFull entry.1) = entry.1 := by
  native_decide

end SmallCusp
