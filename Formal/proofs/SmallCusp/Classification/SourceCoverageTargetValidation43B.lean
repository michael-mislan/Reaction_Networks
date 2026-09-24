import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B1

namespace SmallCusp

def sourceCoverageTargetSlice43B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43B0 ++
  sourceCoverageTargetSlice43B1

theorem sourceCoverageTargetSlice43B_targetConsistent :
    sourceCoverageTargetSlice43B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43B,
    sourceCoverageTargetSlice43B0_targetConsistent,
    sourceCoverageTargetSlice43B1_targetConsistent]

theorem sourceCoverageTargetSlice43B_length : sourceCoverageTargetSlice43B.length = 250 := by
  simp [sourceCoverageTargetSlice43B,
    sourceCoverageTargetSlice43B0_length,
    sourceCoverageTargetSlice43B1_length]

end SmallCusp
