import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A1

namespace SmallCusp

def sourceCoverageTargetSlice57A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57A0 ++
  sourceCoverageTargetSlice57A1

theorem sourceCoverageTargetSlice57A_targetConsistent :
    sourceCoverageTargetSlice57A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57A,
    sourceCoverageTargetSlice57A0_targetConsistent,
    sourceCoverageTargetSlice57A1_targetConsistent]

theorem sourceCoverageTargetSlice57A_length : sourceCoverageTargetSlice57A.length = 250 := by
  simp [sourceCoverageTargetSlice57A,
    sourceCoverageTargetSlice57A0_length,
    sourceCoverageTargetSlice57A1_length]

end SmallCusp
