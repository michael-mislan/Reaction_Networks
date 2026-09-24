import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B1

namespace SmallCusp

def sourceCoverageTargetSlice32B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32B0 ++
  sourceCoverageTargetSlice32B1

theorem sourceCoverageTargetSlice32B_targetConsistent :
    sourceCoverageTargetSlice32B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32B,
    sourceCoverageTargetSlice32B0_targetConsistent,
    sourceCoverageTargetSlice32B1_targetConsistent]

theorem sourceCoverageTargetSlice32B_length : sourceCoverageTargetSlice32B.length = 250 := by
  simp [sourceCoverageTargetSlice32B,
    sourceCoverageTargetSlice32B0_length,
    sourceCoverageTargetSlice32B1_length]

end SmallCusp
