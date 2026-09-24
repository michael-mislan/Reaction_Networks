import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceCoverageBatch56

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_batch56 :
    sourceCoverageBatch56.map sourceRecordKeyPair = sourceRecordKeyPairs56 := by
  native_decide

end SmallCusp
