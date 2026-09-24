import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B11

namespace SmallCusp

def sourceCoverageTargetSlice51B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51B10 ++
  sourceCoverageTargetSlice51B11

theorem sourceCoverageTargetSlice51B1_targetConsistent :
    sourceCoverageTargetSlice51B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51B1,
    sourceCoverageTargetSlice51B10_targetConsistent,
    sourceCoverageTargetSlice51B11_targetConsistent]

theorem sourceCoverageTargetSlice51B1_length : sourceCoverageTargetSlice51B1.length = 125 := by
  simp [sourceCoverageTargetSlice51B1,
    sourceCoverageTargetSlice51B10_length,
    sourceCoverageTargetSlice51B11_length]

end SmallCusp
