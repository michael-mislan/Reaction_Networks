import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B01

namespace SmallCusp

def sourceCoverageTargetSlice31B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31B00 ++
  sourceCoverageTargetSlice31B01

theorem sourceCoverageTargetSlice31B0_targetConsistent :
    sourceCoverageTargetSlice31B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31B0,
    sourceCoverageTargetSlice31B00_targetConsistent,
    sourceCoverageTargetSlice31B01_targetConsistent]

theorem sourceCoverageTargetSlice31B0_length : sourceCoverageTargetSlice31B0.length = 125 := by
  simp [sourceCoverageTargetSlice31B0,
    sourceCoverageTargetSlice31B00_length,
    sourceCoverageTargetSlice31B01_length]

end SmallCusp
