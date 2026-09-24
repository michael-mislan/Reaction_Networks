import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B11

namespace SmallCusp

def sourceCoverageTargetSlice26B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26B10 ++
  sourceCoverageTargetSlice26B11

theorem sourceCoverageTargetSlice26B1_targetConsistent :
    sourceCoverageTargetSlice26B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26B1,
    sourceCoverageTargetSlice26B10_targetConsistent,
    sourceCoverageTargetSlice26B11_targetConsistent]

theorem sourceCoverageTargetSlice26B1_length : sourceCoverageTargetSlice26B1.length = 125 := by
  simp [sourceCoverageTargetSlice26B1,
    sourceCoverageTargetSlice26B10_length,
    sourceCoverageTargetSlice26B11_length]

end SmallCusp
