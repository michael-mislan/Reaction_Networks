import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09B1

namespace SmallCusp

def sourceCoverageTargetSlice09B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice09B0 ++
  sourceCoverageTargetSlice09B1

theorem sourceCoverageTargetSlice09B_targetConsistent :
    sourceCoverageTargetSlice09B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice09B,
    sourceCoverageTargetSlice09B0_targetConsistent,
    sourceCoverageTargetSlice09B1_targetConsistent]

theorem sourceCoverageTargetSlice09B_length : sourceCoverageTargetSlice09B.length = 250 := by
  simp [sourceCoverageTargetSlice09B,
    sourceCoverageTargetSlice09B0_length,
    sourceCoverageTargetSlice09B1_length]

end SmallCusp
