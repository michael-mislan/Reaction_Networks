import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B1

namespace SmallCusp

def sourceCoverageTargetSlice26B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26B0 ++
  sourceCoverageTargetSlice26B1

theorem sourceCoverageTargetSlice26B_targetConsistent :
    sourceCoverageTargetSlice26B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26B,
    sourceCoverageTargetSlice26B0_targetConsistent,
    sourceCoverageTargetSlice26B1_targetConsistent]

theorem sourceCoverageTargetSlice26B_length : sourceCoverageTargetSlice26B.length = 250 := by
  simp [sourceCoverageTargetSlice26B,
    sourceCoverageTargetSlice26B0_length,
    sourceCoverageTargetSlice26B1_length]

end SmallCusp
