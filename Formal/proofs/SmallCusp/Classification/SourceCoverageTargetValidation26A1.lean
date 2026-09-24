import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A11

namespace SmallCusp

def sourceCoverageTargetSlice26A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26A10 ++
  sourceCoverageTargetSlice26A11

theorem sourceCoverageTargetSlice26A1_targetConsistent :
    sourceCoverageTargetSlice26A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26A1,
    sourceCoverageTargetSlice26A10_targetConsistent,
    sourceCoverageTargetSlice26A11_targetConsistent]

theorem sourceCoverageTargetSlice26A1_length : sourceCoverageTargetSlice26A1.length = 125 := by
  simp [sourceCoverageTargetSlice26A1,
    sourceCoverageTargetSlice26A10_length,
    sourceCoverageTargetSlice26A11_length]

end SmallCusp
