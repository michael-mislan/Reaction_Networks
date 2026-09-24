import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21A01

namespace SmallCusp

def sourceCoverageTargetSlice21A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21A00 ++
  sourceCoverageTargetSlice21A01

theorem sourceCoverageTargetSlice21A0_targetConsistent :
    sourceCoverageTargetSlice21A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21A0,
    sourceCoverageTargetSlice21A00_targetConsistent,
    sourceCoverageTargetSlice21A01_targetConsistent]

theorem sourceCoverageTargetSlice21A0_length : sourceCoverageTargetSlice21A0.length = 125 := by
  simp [sourceCoverageTargetSlice21A0,
    sourceCoverageTargetSlice21A00_length,
    sourceCoverageTargetSlice21A01_length]

end SmallCusp
