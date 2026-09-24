import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57B1

namespace SmallCusp

def sourceCoverageTargetSlice57B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57B0 ++
  sourceCoverageTargetSlice57B1

theorem sourceCoverageTargetSlice57B_targetConsistent :
    sourceCoverageTargetSlice57B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57B,
    sourceCoverageTargetSlice57B0_targetConsistent,
    sourceCoverageTargetSlice57B1_targetConsistent]

theorem sourceCoverageTargetSlice57B_length : sourceCoverageTargetSlice57B.length = 250 := by
  simp [sourceCoverageTargetSlice57B,
    sourceCoverageTargetSlice57B0_length,
    sourceCoverageTargetSlice57B1_length]

end SmallCusp
