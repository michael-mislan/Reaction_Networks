import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B1

namespace SmallCusp

def sourceCoverageTargetSlice41B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41B0 ++
  sourceCoverageTargetSlice41B1

theorem sourceCoverageTargetSlice41B_targetConsistent :
    sourceCoverageTargetSlice41B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41B,
    sourceCoverageTargetSlice41B0_targetConsistent,
    sourceCoverageTargetSlice41B1_targetConsistent]

theorem sourceCoverageTargetSlice41B_length : sourceCoverageTargetSlice41B.length = 250 := by
  simp [sourceCoverageTargetSlice41B,
    sourceCoverageTargetSlice41B0_length,
    sourceCoverageTargetSlice41B1_length]

end SmallCusp
