import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43B01

namespace SmallCusp

def sourceCoverageTargetSlice43B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43B00 ++
  sourceCoverageTargetSlice43B01

theorem sourceCoverageTargetSlice43B0_targetConsistent :
    sourceCoverageTargetSlice43B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43B0,
    sourceCoverageTargetSlice43B00_targetConsistent,
    sourceCoverageTargetSlice43B01_targetConsistent]

theorem sourceCoverageTargetSlice43B0_length : sourceCoverageTargetSlice43B0.length = 125 := by
  simp [sourceCoverageTargetSlice43B0,
    sourceCoverageTargetSlice43B00_length,
    sourceCoverageTargetSlice43B01_length]

end SmallCusp
