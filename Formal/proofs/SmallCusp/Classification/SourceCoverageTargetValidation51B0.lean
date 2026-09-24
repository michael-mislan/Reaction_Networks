import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51B01

namespace SmallCusp

def sourceCoverageTargetSlice51B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51B00 ++
  sourceCoverageTargetSlice51B01

theorem sourceCoverageTargetSlice51B0_targetConsistent :
    sourceCoverageTargetSlice51B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51B0,
    sourceCoverageTargetSlice51B00_targetConsistent,
    sourceCoverageTargetSlice51B01_targetConsistent]

theorem sourceCoverageTargetSlice51B0_length : sourceCoverageTargetSlice51B0.length = 125 := by
  simp [sourceCoverageTargetSlice51B0,
    sourceCoverageTargetSlice51B00_length,
    sourceCoverageTargetSlice51B01_length]

end SmallCusp
