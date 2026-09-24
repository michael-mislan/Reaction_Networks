import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A1

namespace SmallCusp

def sourceCoverageTargetSlice26A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26A0 ++
  sourceCoverageTargetSlice26A1

theorem sourceCoverageTargetSlice26A_targetConsistent :
    sourceCoverageTargetSlice26A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26A,
    sourceCoverageTargetSlice26A0_targetConsistent,
    sourceCoverageTargetSlice26A1_targetConsistent]

theorem sourceCoverageTargetSlice26A_length : sourceCoverageTargetSlice26A.length = 250 := by
  simp [sourceCoverageTargetSlice26A,
    sourceCoverageTargetSlice26A0_length,
    sourceCoverageTargetSlice26A1_length]

end SmallCusp
