import proofs.SmallCusp.Classification.SourceRecordKeyPair
import proofs.SmallCusp.Classification.SourceRecordKeyPairsPacked
import proofs.SmallCusp.Classification.SourceCoverageBatch09

namespace SmallCusp

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem source_record_key_pairs_batch09 :
    sourceCoverageBatch09.map sourceRecordKeyPair = sourceRecordKeyPairs09 := by
  native_decide

end SmallCusp
