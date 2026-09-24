import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation26B01

namespace SmallCusp

def sourceCoverageTargetSlice26B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice26B00 ++
  sourceCoverageTargetSlice26B01

theorem sourceCoverageTargetSlice26B0_targetConsistent :
    sourceCoverageTargetSlice26B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice26B0,
    sourceCoverageTargetSlice26B00_targetConsistent,
    sourceCoverageTargetSlice26B01_targetConsistent]

theorem sourceCoverageTargetSlice26B0_length : sourceCoverageTargetSlice26B0.length = 125 := by
  simp [sourceCoverageTargetSlice26B0,
    sourceCoverageTargetSlice26B00_length,
    sourceCoverageTargetSlice26B01_length]

end SmallCusp
