import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation51A1

namespace SmallCusp

def sourceCoverageTargetSlice51A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice51A0 ++
  sourceCoverageTargetSlice51A1

theorem sourceCoverageTargetSlice51A_targetConsistent :
    sourceCoverageTargetSlice51A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice51A,
    sourceCoverageTargetSlice51A0_targetConsistent,
    sourceCoverageTargetSlice51A1_targetConsistent]

theorem sourceCoverageTargetSlice51A_length : sourceCoverageTargetSlice51A.length = 250 := by
  simp [sourceCoverageTargetSlice51A,
    sourceCoverageTargetSlice51A0_length,
    sourceCoverageTargetSlice51A1_length]

end SmallCusp
