import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A1

namespace SmallCusp

def sourceCoverageTargetSlice31A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31A0 ++
  sourceCoverageTargetSlice31A1

theorem sourceCoverageTargetSlice31A_targetConsistent :
    sourceCoverageTargetSlice31A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31A,
    sourceCoverageTargetSlice31A0_targetConsistent,
    sourceCoverageTargetSlice31A1_targetConsistent]

theorem sourceCoverageTargetSlice31A_length : sourceCoverageTargetSlice31A.length = 250 := by
  simp [sourceCoverageTargetSlice31A,
    sourceCoverageTargetSlice31A0_length,
    sourceCoverageTargetSlice31A1_length]

end SmallCusp
