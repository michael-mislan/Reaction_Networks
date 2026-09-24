import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B01

namespace SmallCusp

def sourceCoverageTargetSlice21B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21B00 ++
  sourceCoverageTargetSlice21B01

theorem sourceCoverageTargetSlice21B0_targetConsistent :
    sourceCoverageTargetSlice21B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21B0,
    sourceCoverageTargetSlice21B00_targetConsistent,
    sourceCoverageTargetSlice21B01_targetConsistent]

theorem sourceCoverageTargetSlice21B0_length : sourceCoverageTargetSlice21B0.length = 125 := by
  simp [sourceCoverageTargetSlice21B0,
    sourceCoverageTargetSlice21B00_length,
    sourceCoverageTargetSlice21B01_length]

end SmallCusp
