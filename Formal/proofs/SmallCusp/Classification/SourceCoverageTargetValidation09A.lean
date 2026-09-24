import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation09A1

namespace SmallCusp

def sourceCoverageTargetSlice09A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice09A0 ++
  sourceCoverageTargetSlice09A1

theorem sourceCoverageTargetSlice09A_targetConsistent :
    sourceCoverageTargetSlice09A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice09A,
    sourceCoverageTargetSlice09A0_targetConsistent,
    sourceCoverageTargetSlice09A1_targetConsistent]

theorem sourceCoverageTargetSlice09A_length : sourceCoverageTargetSlice09A.length = 250 := by
  simp [sourceCoverageTargetSlice09A,
    sourceCoverageTargetSlice09A0_length,
    sourceCoverageTargetSlice09A1_length]

end SmallCusp
