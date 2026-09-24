import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation57A01

namespace SmallCusp

def sourceCoverageTargetSlice57A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice57A00 ++
  sourceCoverageTargetSlice57A01

theorem sourceCoverageTargetSlice57A0_targetConsistent :
    sourceCoverageTargetSlice57A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice57A0,
    sourceCoverageTargetSlice57A00_targetConsistent,
    sourceCoverageTargetSlice57A01_targetConsistent]

theorem sourceCoverageTargetSlice57A0_length : sourceCoverageTargetSlice57A0.length = 125 := by
  simp [sourceCoverageTargetSlice57A0,
    sourceCoverageTargetSlice57A00_length,
    sourceCoverageTargetSlice57A01_length]

end SmallCusp
