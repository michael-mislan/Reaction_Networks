import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B11

namespace SmallCusp

def sourceCoverageTargetSlice43B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43B10 ++
  sourceCoverageTargetSlice43B11

theorem sourceCoverageTargetSlice43B1_targetConsistent :
    sourceCoverageTargetSlice43B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43B1,
    sourceCoverageTargetSlice43B10_targetConsistent,
    sourceCoverageTargetSlice43B11_targetConsistent]

theorem sourceCoverageTargetSlice43B1_length : sourceCoverageTargetSlice43B1.length = 125 := by
  simp [sourceCoverageTargetSlice43B1,
    sourceCoverageTargetSlice43B10_length,
    sourceCoverageTargetSlice43B11_length]

end SmallCusp
