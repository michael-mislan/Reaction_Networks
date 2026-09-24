import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A11

namespace SmallCusp

def sourceCoverageTargetSlice56A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56A10 ++
  sourceCoverageTargetSlice56A11

theorem sourceCoverageTargetSlice56A1_targetConsistent :
    sourceCoverageTargetSlice56A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56A1,
    sourceCoverageTargetSlice56A10_targetConsistent,
    sourceCoverageTargetSlice56A11_targetConsistent]

theorem sourceCoverageTargetSlice56A1_length : sourceCoverageTargetSlice56A1.length = 125 := by
  simp [sourceCoverageTargetSlice56A1,
    sourceCoverageTargetSlice56A10_length,
    sourceCoverageTargetSlice56A11_length]

end SmallCusp
