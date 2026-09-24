import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B1

namespace SmallCusp

def sourceCoverageTargetSlice37B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37B0 ++
  sourceCoverageTargetSlice37B1

theorem sourceCoverageTargetSlice37B_targetConsistent :
    sourceCoverageTargetSlice37B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37B,
    sourceCoverageTargetSlice37B0_targetConsistent,
    sourceCoverageTargetSlice37B1_targetConsistent]

theorem sourceCoverageTargetSlice37B_length : sourceCoverageTargetSlice37B.length = 250 := by
  simp [sourceCoverageTargetSlice37B,
    sourceCoverageTargetSlice37B0_length,
    sourceCoverageTargetSlice37B1_length]

end SmallCusp
