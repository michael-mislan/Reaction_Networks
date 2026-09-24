import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B11

namespace SmallCusp

def sourceCoverageTargetSlice57B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57B10 ++
  sourceCoverageTargetSlice57B11

theorem sourceCoverageTargetSlice57B1_targetConsistent :
    sourceCoverageTargetSlice57B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57B1,
    sourceCoverageTargetSlice57B10_targetConsistent,
    sourceCoverageTargetSlice57B11_targetConsistent]

theorem sourceCoverageTargetSlice57B1_length : sourceCoverageTargetSlice57B1.length = 125 := by
  simp [sourceCoverageTargetSlice57B1,
    sourceCoverageTargetSlice57B10_length,
    sourceCoverageTargetSlice57B11_length]

end SmallCusp
