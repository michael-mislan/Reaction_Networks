import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19B01

namespace SmallCusp

def sourceCoverageTargetSlice19B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19B00 ++
  sourceCoverageTargetSlice19B01

theorem sourceCoverageTargetSlice19B0_targetConsistent :
    sourceCoverageTargetSlice19B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19B0,
    sourceCoverageTargetSlice19B00_targetConsistent,
    sourceCoverageTargetSlice19B01_targetConsistent]

theorem sourceCoverageTargetSlice19B0_length : sourceCoverageTargetSlice19B0.length = 125 := by
  simp [sourceCoverageTargetSlice19B0,
    sourceCoverageTargetSlice19B00_length,
    sourceCoverageTargetSlice19B01_length]

end SmallCusp
