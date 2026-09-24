import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceLookupTable

namespace SmallCusp

def lookupPayloadKeyPairsValid (entries : Array (Nat × Nat × Bool))
    (pairs : Array (Nat × Nat)) : Bool :=
  entries.all fun entry =>
    match pairs[entry.2.1]? with
    | none => false
    | some pair => (if entry.2.2 then pair.2 else pair.1) == entry.1

theorem source_lookup_packed_payload_keys_valid :
    lookupPayloadKeyPairsValid sourceLookupEntries sourceRecordKeyPairs.toArray = true := by
  native_decide

end SmallCusp
