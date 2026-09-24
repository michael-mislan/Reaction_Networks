import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B11

namespace SmallCusp

def sourceCoverageTargetSlice19B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19B10 ++
  sourceCoverageTargetSlice19B11

theorem sourceCoverageTargetSlice19B1_targetConsistent :
    sourceCoverageTargetSlice19B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19B1,
    sourceCoverageTargetSlice19B10_targetConsistent,
    sourceCoverageTargetSlice19B11_targetConsistent]

theorem sourceCoverageTargetSlice19B1_length : sourceCoverageTargetSlice19B1.length = 125 := by
  simp [sourceCoverageTargetSlice19B1,
    sourceCoverageTargetSlice19B10_length,
    sourceCoverageTargetSlice19B11_length]

end SmallCusp
