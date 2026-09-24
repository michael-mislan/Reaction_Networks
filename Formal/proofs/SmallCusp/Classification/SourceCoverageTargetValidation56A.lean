import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A1

namespace SmallCusp

def sourceCoverageTargetSlice56A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56A0 ++
  sourceCoverageTargetSlice56A1

theorem sourceCoverageTargetSlice56A_targetConsistent :
    sourceCoverageTargetSlice56A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56A,
    sourceCoverageTargetSlice56A0_targetConsistent,
    sourceCoverageTargetSlice56A1_targetConsistent]

theorem sourceCoverageTargetSlice56A_length : sourceCoverageTargetSlice56A.length = 250 := by
  simp [sourceCoverageTargetSlice56A,
    sourceCoverageTargetSlice56A0_length,
    sourceCoverageTargetSlice56A1_length]

end SmallCusp
