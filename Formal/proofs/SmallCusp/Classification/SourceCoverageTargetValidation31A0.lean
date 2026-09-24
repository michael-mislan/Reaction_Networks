import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation31A01

namespace SmallCusp

def sourceCoverageTargetSlice31A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice31A00 ++
  sourceCoverageTargetSlice31A01

theorem sourceCoverageTargetSlice31A0_targetConsistent :
    sourceCoverageTargetSlice31A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice31A0,
    sourceCoverageTargetSlice31A00_targetConsistent,
    sourceCoverageTargetSlice31A01_targetConsistent]

theorem sourceCoverageTargetSlice31A0_length : sourceCoverageTargetSlice31A0.length = 125 := by
  simp [sourceCoverageTargetSlice31A0,
    sourceCoverageTargetSlice31A00_length,
    sourceCoverageTargetSlice31A01_length]

end SmallCusp
