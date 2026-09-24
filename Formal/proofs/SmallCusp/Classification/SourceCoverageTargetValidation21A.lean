import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A1

namespace SmallCusp

def sourceCoverageTargetSlice21A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21A0 ++
  sourceCoverageTargetSlice21A1

theorem sourceCoverageTargetSlice21A_targetConsistent :
    sourceCoverageTargetSlice21A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21A,
    sourceCoverageTargetSlice21A0_targetConsistent,
    sourceCoverageTargetSlice21A1_targetConsistent]

theorem sourceCoverageTargetSlice21A_length : sourceCoverageTargetSlice21A.length = 250 := by
  simp [sourceCoverageTargetSlice21A,
    sourceCoverageTargetSlice21A0_length,
    sourceCoverageTargetSlice21A1_length]

end SmallCusp
