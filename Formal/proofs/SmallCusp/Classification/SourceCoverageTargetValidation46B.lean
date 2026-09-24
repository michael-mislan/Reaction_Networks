import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B1

namespace SmallCusp

def sourceCoverageTargetSlice46B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46B0 ++
  sourceCoverageTargetSlice46B1

theorem sourceCoverageTargetSlice46B_targetConsistent :
    sourceCoverageTargetSlice46B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46B,
    sourceCoverageTargetSlice46B0_targetConsistent,
    sourceCoverageTargetSlice46B1_targetConsistent]

theorem sourceCoverageTargetSlice46B_length : sourceCoverageTargetSlice46B.length = 250 := by
  simp [sourceCoverageTargetSlice46B,
    sourceCoverageTargetSlice46B0_length,
    sourceCoverageTargetSlice46B1_length]

end SmallCusp
