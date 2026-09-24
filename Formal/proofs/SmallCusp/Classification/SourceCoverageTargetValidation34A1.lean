import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A11

namespace SmallCusp

def sourceCoverageTargetSlice34A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34A10 ++
  sourceCoverageTargetSlice34A11

theorem sourceCoverageTargetSlice34A1_targetConsistent :
    sourceCoverageTargetSlice34A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34A1,
    sourceCoverageTargetSlice34A10_targetConsistent,
    sourceCoverageTargetSlice34A11_targetConsistent]

theorem sourceCoverageTargetSlice34A1_length : sourceCoverageTargetSlice34A1.length = 125 := by
  simp [sourceCoverageTargetSlice34A1,
    sourceCoverageTargetSlice34A10_length,
    sourceCoverageTargetSlice34A11_length]

end SmallCusp
