import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A11

namespace SmallCusp

def sourceCoverageTargetSlice41A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41A10 ++
  sourceCoverageTargetSlice41A11

theorem sourceCoverageTargetSlice41A1_targetConsistent :
    sourceCoverageTargetSlice41A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41A1,
    sourceCoverageTargetSlice41A10_targetConsistent,
    sourceCoverageTargetSlice41A11_targetConsistent]

theorem sourceCoverageTargetSlice41A1_length : sourceCoverageTargetSlice41A1.length = 125 := by
  simp [sourceCoverageTargetSlice41A1,
    sourceCoverageTargetSlice41A10_length,
    sourceCoverageTargetSlice41A11_length]

end SmallCusp
