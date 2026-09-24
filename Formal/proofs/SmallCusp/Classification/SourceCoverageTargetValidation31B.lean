import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31B1

namespace SmallCusp

def sourceCoverageTargetSlice31B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31B0 ++
  sourceCoverageTargetSlice31B1

theorem sourceCoverageTargetSlice31B_targetConsistent :
    sourceCoverageTargetSlice31B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31B,
    sourceCoverageTargetSlice31B0_targetConsistent,
    sourceCoverageTargetSlice31B1_targetConsistent]

theorem sourceCoverageTargetSlice31B_length : sourceCoverageTargetSlice31B.length = 250 := by
  simp [sourceCoverageTargetSlice31B,
    sourceCoverageTargetSlice31B0_length,
    sourceCoverageTargetSlice31B1_length]

end SmallCusp
