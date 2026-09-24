import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B1

namespace SmallCusp

def sourceCoverageTargetSlice21B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21B0 ++
  sourceCoverageTargetSlice21B1

theorem sourceCoverageTargetSlice21B_targetConsistent :
    sourceCoverageTargetSlice21B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21B,
    sourceCoverageTargetSlice21B0_targetConsistent,
    sourceCoverageTargetSlice21B1_targetConsistent]

theorem sourceCoverageTargetSlice21B_length : sourceCoverageTargetSlice21B.length = 250 := by
  simp [sourceCoverageTargetSlice21B,
    sourceCoverageTargetSlice21B0_length,
    sourceCoverageTargetSlice21B1_length]

end SmallCusp
