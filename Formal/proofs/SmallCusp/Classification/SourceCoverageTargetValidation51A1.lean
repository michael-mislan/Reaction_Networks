import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A11

namespace SmallCusp

def sourceCoverageTargetSlice51A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51A10 ++
  sourceCoverageTargetSlice51A11

theorem sourceCoverageTargetSlice51A1_targetConsistent :
    sourceCoverageTargetSlice51A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51A1,
    sourceCoverageTargetSlice51A10_targetConsistent,
    sourceCoverageTargetSlice51A11_targetConsistent]

theorem sourceCoverageTargetSlice51A1_length : sourceCoverageTargetSlice51A1.length = 125 := by
  simp [sourceCoverageTargetSlice51A1,
    sourceCoverageTargetSlice51A10_length,
    sourceCoverageTargetSlice51A11_length]

end SmallCusp
