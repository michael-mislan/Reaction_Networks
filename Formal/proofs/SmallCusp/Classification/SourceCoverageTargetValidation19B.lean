import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B1

namespace SmallCusp

def sourceCoverageTargetSlice19B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19B0 ++
  sourceCoverageTargetSlice19B1

theorem sourceCoverageTargetSlice19B_targetConsistent :
    sourceCoverageTargetSlice19B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19B,
    sourceCoverageTargetSlice19B0_targetConsistent,
    sourceCoverageTargetSlice19B1_targetConsistent]

theorem sourceCoverageTargetSlice19B_length : sourceCoverageTargetSlice19B.length = 250 := by
  simp [sourceCoverageTargetSlice19B,
    sourceCoverageTargetSlice19B0_length,
    sourceCoverageTargetSlice19B1_length]

end SmallCusp
