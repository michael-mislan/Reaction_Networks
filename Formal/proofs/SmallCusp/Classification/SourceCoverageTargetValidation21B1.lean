import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation21B11

namespace SmallCusp

def sourceCoverageTargetSlice21B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice21B10 ++
  sourceCoverageTargetSlice21B11

theorem sourceCoverageTargetSlice21B1_targetConsistent :
    sourceCoverageTargetSlice21B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice21B1,
    sourceCoverageTargetSlice21B10_targetConsistent,
    sourceCoverageTargetSlice21B11_targetConsistent]

theorem sourceCoverageTargetSlice21B1_length : sourceCoverageTargetSlice21B1.length = 125 := by
  simp [sourceCoverageTargetSlice21B1,
    sourceCoverageTargetSlice21B10_length,
    sourceCoverageTargetSlice21B11_length]

end SmallCusp
