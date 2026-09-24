import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation10B1

namespace SmallCusp

def sourceCoverageTargetSlice10B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice10B0 ++
  sourceCoverageTargetSlice10B1

theorem sourceCoverageTargetSlice10B_targetConsistent :
    sourceCoverageTargetSlice10B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice10B,
    sourceCoverageTargetSlice10B0_targetConsistent,
    sourceCoverageTargetSlice10B1_targetConsistent]

theorem sourceCoverageTargetSlice10B_length : sourceCoverageTargetSlice10B.length = 250 := by
  simp [sourceCoverageTargetSlice10B,
    sourceCoverageTargetSlice10B0_length,
    sourceCoverageTargetSlice10B1_length]

end SmallCusp
