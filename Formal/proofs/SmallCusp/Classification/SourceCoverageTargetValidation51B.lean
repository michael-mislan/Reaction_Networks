import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B1

namespace SmallCusp

def sourceCoverageTargetSlice51B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51B0 ++
  sourceCoverageTargetSlice51B1

theorem sourceCoverageTargetSlice51B_targetConsistent :
    sourceCoverageTargetSlice51B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51B,
    sourceCoverageTargetSlice51B0_targetConsistent,
    sourceCoverageTargetSlice51B1_targetConsistent]

theorem sourceCoverageTargetSlice51B_length : sourceCoverageTargetSlice51B.length = 250 := by
  simp [sourceCoverageTargetSlice51B,
    sourceCoverageTargetSlice51B0_length,
    sourceCoverageTargetSlice51B1_length]

end SmallCusp
