import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceCoverageBatch37

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_batch37 :
    sourceCoverageBatch37.map sourceRecordKeyPair = sourceRecordKeyPairs37 := by
  native_decide

end SmallCusp
