import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation43A01

namespace SmallCusp

def sourceCoverageTargetSlice43A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice43A00 ++
  sourceCoverageTargetSlice43A01

theorem sourceCoverageTargetSlice43A0_targetConsistent :
    sourceCoverageTargetSlice43A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice43A0,
    sourceCoverageTargetSlice43A00_targetConsistent,
    sourceCoverageTargetSlice43A01_targetConsistent]

theorem sourceCoverageTargetSlice43A0_length : sourceCoverageTargetSlice43A0.length = 125 := by
  simp [sourceCoverageTargetSlice43A0,
    sourceCoverageTargetSlice43A00_length,
    sourceCoverageTargetSlice43A01_length]

end SmallCusp
