import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceCoverageBatch59

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_batch59 :
    sourceCoverageBatch59.map sourceRecordKeyPair = sourceRecordKeyPairs59 := by
  native_decide

end SmallCusp
