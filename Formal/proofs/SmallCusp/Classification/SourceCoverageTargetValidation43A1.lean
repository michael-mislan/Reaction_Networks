import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A11

namespace SmallCusp

def sourceCoverageTargetSlice43A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43A10 ++
  sourceCoverageTargetSlice43A11

theorem sourceCoverageTargetSlice43A1_targetConsistent :
    sourceCoverageTargetSlice43A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43A1,
    sourceCoverageTargetSlice43A10_targetConsistent,
    sourceCoverageTargetSlice43A11_targetConsistent]

theorem sourceCoverageTargetSlice43A1_length : sourceCoverageTargetSlice43A1.length = 125 := by
  simp [sourceCoverageTargetSlice43A1,
    sourceCoverageTargetSlice43A10_length,
    sourceCoverageTargetSlice43A11_length]

end SmallCusp
