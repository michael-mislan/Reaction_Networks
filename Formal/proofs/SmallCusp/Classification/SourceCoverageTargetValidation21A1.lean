import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A11

namespace SmallCusp

def sourceCoverageTargetSlice21A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21A10 ++
  sourceCoverageTargetSlice21A11

theorem sourceCoverageTargetSlice21A1_targetConsistent :
    sourceCoverageTargetSlice21A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21A1,
    sourceCoverageTargetSlice21A10_targetConsistent,
    sourceCoverageTargetSlice21A11_targetConsistent]

theorem sourceCoverageTargetSlice21A1_length : sourceCoverageTargetSlice21A1.length = 125 := by
  simp [sourceCoverageTargetSlice21A1,
    sourceCoverageTargetSlice21A10_length,
    sourceCoverageTargetSlice21A11_length]

end SmallCusp
