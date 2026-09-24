import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceCoverageBatch16

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_batch16 :
    sourceCoverageBatch16.map sourceRecordKeyPair = sourceRecordKeyPairs16 := by
  native_decide

end SmallCusp
