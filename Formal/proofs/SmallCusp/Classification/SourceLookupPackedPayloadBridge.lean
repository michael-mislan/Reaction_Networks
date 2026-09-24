import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceLookupPackedPayloadCheck

namespace SmallCusp

theorem lookup_payload_identity_of_pair_map
    (records : Array SourceCoverageRecord) (pairs : Array (Nat × Nat))
    (entries : Array (Nat × Nat × Bool))
    (hmap : records.map sourceRecordKeyPair = pairs)
    (hvalid : ∀ (j : Nat) (R : SourceCoverageRecord), records[j]? = some R → R.Docked)
    (hcheck : lookupPayloadKeyPairsValid entries pairs = true)
    (i : Fin entries.size) :
    ∃ R : SourceCoverageRecord, records[(entries[i.val]!).2.1]? = some R ∧
      bimolCatalogueKey
        (if (entries[i.val]!).2.2 then
          codedReactionSet (swapCodedNetwork R.sourceNetwork)
        else codedReactionSet R.sourceNetwork) = (entries[i.val]!).1 := by
  have hc := Array.all_eq_true.mp hcheck i.val i.isLt
  have hc' : (match pairs[(entries[i.val]!).2.1]? with
    | none => false
    | some pair => (if (entries[i.val]!).2.2 then pair.2 else pair.1) ==
        (entries[i.val]!).1) = true := by
    simpa only [getElem!_pos entries i.val i.isLt] using hc
  rw [← hmap, Array.getElem?_map] at hc'
  cases hr : records[(entries[i.val]!).2.1]? with
  | none => simp only [hr, Option.map_none, Bool.false_eq_true] at hc'
  | some R =>
      simp only [hr, Option.map_some, beq_iff_eq] at hc'
      have hd := hvalid _ R hr
      refine ⟨R, rfl, ?_⟩
      cases hb : (entries[i.val]!).2.2
      · simpa only [hb, Bool.false_eq_true, if_false, source_record_key_pair_canonical R hd] using hc'
      · simpa only [hb, if_true, source_record_key_pair_swapped R hd] using hc'

end SmallCusp
