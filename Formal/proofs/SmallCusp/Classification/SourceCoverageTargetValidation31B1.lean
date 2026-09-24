import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B11

namespace SmallCusp

def sourceCoverageTargetSlice31B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31B10 ++
  sourceCoverageTargetSlice31B11

theorem sourceCoverageTargetSlice31B1_targetConsistent :
    sourceCoverageTargetSlice31B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31B1,
    sourceCoverageTargetSlice31B10_targetConsistent,
    sourceCoverageTargetSlice31B11_targetConsistent]

theorem sourceCoverageTargetSlice31B1_length : sourceCoverageTargetSlice31B1.length = 125 := by
  simp [sourceCoverageTargetSlice31B1,
    sourceCoverageTargetSlice31B10_length,
    sourceCoverageTargetSlice31B11_length]

end SmallCusp
