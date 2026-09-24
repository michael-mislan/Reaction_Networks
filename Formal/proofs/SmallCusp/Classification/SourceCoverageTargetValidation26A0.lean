import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26A01

namespace SmallCusp

def sourceCoverageTargetSlice26A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26A00 ++
  sourceCoverageTargetSlice26A01

theorem sourceCoverageTargetSlice26A0_targetConsistent :
    sourceCoverageTargetSlice26A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26A0,
    sourceCoverageTargetSlice26A00_targetConsistent,
    sourceCoverageTargetSlice26A01_targetConsistent]

theorem sourceCoverageTargetSlice26A0_length : sourceCoverageTargetSlice26A0.length = 125 := by
  simp [sourceCoverageTargetSlice26A0,
    sourceCoverageTargetSlice26A00_length,
    sourceCoverageTargetSlice26A01_length]

end SmallCusp
