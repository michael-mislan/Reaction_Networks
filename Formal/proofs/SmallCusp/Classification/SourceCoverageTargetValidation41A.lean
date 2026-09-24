import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation41A1

namespace SmallCusp

def sourceCoverageTargetSlice41A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice41A0 ++
  sourceCoverageTargetSlice41A1

theorem sourceCoverageTargetSlice41A_targetConsistent :
    sourceCoverageTargetSlice41A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice41A,
    sourceCoverageTargetSlice41A0_targetConsistent,
    sourceCoverageTargetSlice41A1_targetConsistent]

theorem sourceCoverageTargetSlice41A_length : sourceCoverageTargetSlice41A.length = 250 := by
  simp [sourceCoverageTargetSlice41A,
    sourceCoverageTargetSlice41A0_length,
    sourceCoverageTargetSlice41A1_length]

end SmallCusp
