import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41B01

namespace SmallCusp

def sourceCoverageTargetSlice41B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41B00 ++
  sourceCoverageTargetSlice41B01

theorem sourceCoverageTargetSlice41B0_targetConsistent :
    sourceCoverageTargetSlice41B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41B0,
    sourceCoverageTargetSlice41B00_targetConsistent,
    sourceCoverageTargetSlice41B01_targetConsistent]

theorem sourceCoverageTargetSlice41B0_length : sourceCoverageTargetSlice41B0.length = 125 := by
  simp [sourceCoverageTargetSlice41B0,
    sourceCoverageTargetSlice41B00_length,
    sourceCoverageTargetSlice41B01_length]

end SmallCusp
