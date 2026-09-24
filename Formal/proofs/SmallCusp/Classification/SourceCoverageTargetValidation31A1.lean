import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A11

namespace SmallCusp

def sourceCoverageTargetSlice31A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31A10 ++
  sourceCoverageTargetSlice31A11

theorem sourceCoverageTargetSlice31A1_targetConsistent :
    sourceCoverageTargetSlice31A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31A1,
    sourceCoverageTargetSlice31A10_targetConsistent,
    sourceCoverageTargetSlice31A11_targetConsistent]

theorem sourceCoverageTargetSlice31A1_length : sourceCoverageTargetSlice31A1.length = 125 := by
  simp [sourceCoverageTargetSlice31A1,
    sourceCoverageTargetSlice31A10_length,
    sourceCoverageTargetSlice31A11_length]

end SmallCusp
