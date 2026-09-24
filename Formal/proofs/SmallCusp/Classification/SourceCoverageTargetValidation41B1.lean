import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B11

namespace SmallCusp

def sourceCoverageTargetSlice41B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41B10 ++
  sourceCoverageTargetSlice41B11

theorem sourceCoverageTargetSlice41B1_targetConsistent :
    sourceCoverageTargetSlice41B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41B1,
    sourceCoverageTargetSlice41B10_targetConsistent,
    sourceCoverageTargetSlice41B11_targetConsistent]

theorem sourceCoverageTargetSlice41B1_length : sourceCoverageTargetSlice41B1.length = 125 := by
  simp [sourceCoverageTargetSlice41B1,
    sourceCoverageTargetSlice41B10_length,
    sourceCoverageTargetSlice41B11_length]

end SmallCusp
