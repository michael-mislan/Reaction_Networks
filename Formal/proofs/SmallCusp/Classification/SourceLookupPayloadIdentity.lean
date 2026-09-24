import proofs.SmallCusp.Classification.SourceRecordKeyPairsAll
import proofs.SmallCusp.Classification.SourceLookupPackedPayloadBridge
import proofs.SmallCusp.Classification.SourceLookupPayloadCoverage

namespace SmallCusp

theorem source_lookup_payload_identity
    (recordsValid : sourceCoverageRecords.all (fun R => decide R.Valid) = true) :
    SourceLookupPayloadIdentity := by
  have hmap : sourceCoverageArray.map sourceRecordKeyPair =
      sourceRecordKeyPairs.toArray := by
    simpa only [sourceCoverageArray, List.map_toArray] using
      congrArg List.toArray source_record_key_pairs_all
  intro i
  exact lookup_payload_identity_of_pair_map sourceCoverageArray
    sourceRecordKeyPairs.toArray sourceLookupEntries hmap
    (fun _ _ h => (sourceCoverageArray_valid_of_checks recordsValid h).1)
    source_lookup_packed_payload_keys_valid i

end SmallCusp
