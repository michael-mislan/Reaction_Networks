import proofs.SmallCusp.Classification.SourceCoverageBatch00
import proofs.SmallCusp.Classification.SourceCoverageSourceIndices00

namespace SmallCusp

def sourceCoverageBatch00IndexRows : Array (Array Nat) :=
  sourceCoverageBatch00.toArray.map
    (fun R => Array.ofFn (fun i => (R.sourceIndices i).val))

def sourceCoverageBatch00IndexRowsValid : Bool :=
  sourceCoverageBatch00IndexRows == sourceCoverageSourceIndices00

theorem source_coverage_batch00_indices_match_literals :
    sourceCoverageBatch00IndexRowsValid = true := by
  native_decide

end SmallCusp
