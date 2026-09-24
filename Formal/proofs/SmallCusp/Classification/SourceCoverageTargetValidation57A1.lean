import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A11

namespace SmallCusp

def sourceCoverageTargetSlice57A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57A10 ++
  sourceCoverageTargetSlice57A11

theorem sourceCoverageTargetSlice57A1_targetConsistent :
    sourceCoverageTargetSlice57A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57A1,
    sourceCoverageTargetSlice57A10_targetConsistent,
    sourceCoverageTargetSlice57A11_targetConsistent]

theorem sourceCoverageTargetSlice57A1_length : sourceCoverageTargetSlice57A1.length = 125 := by
  simp [sourceCoverageTargetSlice57A1,
    sourceCoverageTargetSlice57A10_length,
    sourceCoverageTargetSlice57A11_length]

end SmallCusp
