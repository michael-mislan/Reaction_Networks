import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B1

namespace SmallCusp

def sourceCoverageTargetSlice28B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28B0 ++
  sourceCoverageTargetSlice28B1

theorem sourceCoverageTargetSlice28B_targetConsistent :
    sourceCoverageTargetSlice28B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28B,
    sourceCoverageTargetSlice28B0_targetConsistent,
    sourceCoverageTargetSlice28B1_targetConsistent]

theorem sourceCoverageTargetSlice28B_length : sourceCoverageTargetSlice28B.length = 250 := by
  simp [sourceCoverageTargetSlice28B,
    sourceCoverageTargetSlice28B0_length,
    sourceCoverageTargetSlice28B1_length]

end SmallCusp
