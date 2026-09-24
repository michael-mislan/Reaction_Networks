import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A01

namespace SmallCusp

def sourceCoverageTargetSlice51A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51A00 ++
  sourceCoverageTargetSlice51A01

theorem sourceCoverageTargetSlice51A0_targetConsistent :
    sourceCoverageTargetSlice51A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51A0,
    sourceCoverageTargetSlice51A00_targetConsistent,
    sourceCoverageTargetSlice51A01_targetConsistent]

theorem sourceCoverageTargetSlice51A0_length : sourceCoverageTargetSlice51A0.length = 125 := by
  simp [sourceCoverageTargetSlice51A0,
    sourceCoverageTargetSlice51A00_length,
    sourceCoverageTargetSlice51A01_length]

end SmallCusp
