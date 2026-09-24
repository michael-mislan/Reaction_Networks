import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B11

namespace SmallCusp

def sourceCoverageTargetSlice28B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28B10 ++
  sourceCoverageTargetSlice28B11

theorem sourceCoverageTargetSlice28B1_targetConsistent :
    sourceCoverageTargetSlice28B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28B1,
    sourceCoverageTargetSlice28B10_targetConsistent,
    sourceCoverageTargetSlice28B11_targetConsistent]

theorem sourceCoverageTargetSlice28B1_length : sourceCoverageTargetSlice28B1.length = 125 := by
  simp [sourceCoverageTargetSlice28B1,
    sourceCoverageTargetSlice28B10_length,
    sourceCoverageTargetSlice28B11_length]

end SmallCusp
