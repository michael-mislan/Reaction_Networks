import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B01

namespace SmallCusp

def sourceCoverageTargetSlice57B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57B00 ++
  sourceCoverageTargetSlice57B01

theorem sourceCoverageTargetSlice57B0_targetConsistent :
    sourceCoverageTargetSlice57B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57B0,
    sourceCoverageTargetSlice57B00_targetConsistent,
    sourceCoverageTargetSlice57B01_targetConsistent]

theorem sourceCoverageTargetSlice57B0_length : sourceCoverageTargetSlice57B0.length = 125 := by
  simp [sourceCoverageTargetSlice57B0,
    sourceCoverageTargetSlice57B00_length,
    sourceCoverageTargetSlice57B01_length]

end SmallCusp
