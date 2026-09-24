import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10A1

namespace SmallCusp

def sourceCoverageTargetSlice10A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice10A0 ++
  sourceCoverageTargetSlice10A1

theorem sourceCoverageTargetSlice10A_targetConsistent :
    sourceCoverageTargetSlice10A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice10A,
    sourceCoverageTargetSlice10A0_targetConsistent,
    sourceCoverageTargetSlice10A1_targetConsistent]

theorem sourceCoverageTargetSlice10A_length : sourceCoverageTargetSlice10A.length = 250 := by
  simp [sourceCoverageTargetSlice10A,
    sourceCoverageTargetSlice10A0_length,
    sourceCoverageTargetSlice10A1_length]

end SmallCusp
