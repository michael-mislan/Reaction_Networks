import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A1

namespace SmallCusp

def sourceCoverageTargetSlice43A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43A0 ++
  sourceCoverageTargetSlice43A1

theorem sourceCoverageTargetSlice43A_targetConsistent :
    sourceCoverageTargetSlice43A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43A,
    sourceCoverageTargetSlice43A0_targetConsistent,
    sourceCoverageTargetSlice43A1_targetConsistent]

theorem sourceCoverageTargetSlice43A_length : sourceCoverageTargetSlice43A.length = 250 := by
  simp [sourceCoverageTargetSlice43A,
    sourceCoverageTargetSlice43A0_length,
    sourceCoverageTargetSlice43A1_length]

end SmallCusp
