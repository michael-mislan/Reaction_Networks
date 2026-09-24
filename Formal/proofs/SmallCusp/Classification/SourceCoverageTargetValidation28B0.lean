import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28B01

namespace SmallCusp

def sourceCoverageTargetSlice28B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28B00 ++
  sourceCoverageTargetSlice28B01

theorem sourceCoverageTargetSlice28B0_targetConsistent :
    sourceCoverageTargetSlice28B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28B0,
    sourceCoverageTargetSlice28B00_targetConsistent,
    sourceCoverageTargetSlice28B01_targetConsistent]

theorem sourceCoverageTargetSlice28B0_length : sourceCoverageTargetSlice28B0.length = 125 := by
  simp [sourceCoverageTargetSlice28B0,
    sourceCoverageTargetSlice28B00_length,
    sourceCoverageTargetSlice28B01_length]

end SmallCusp
