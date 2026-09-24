import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A01

namespace SmallCusp

def sourceCoverageTargetSlice41A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41A00 ++
  sourceCoverageTargetSlice41A01

theorem sourceCoverageTargetSlice41A0_targetConsistent :
    sourceCoverageTargetSlice41A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41A0,
    sourceCoverageTargetSlice41A00_targetConsistent,
    sourceCoverageTargetSlice41A01_targetConsistent]

theorem sourceCoverageTargetSlice41A0_length : sourceCoverageTargetSlice41A0.length = 125 := by
  simp [sourceCoverageTargetSlice41A0,
    sourceCoverageTargetSlice41A00_length,
    sourceCoverageTargetSlice41A01_length]

end SmallCusp
