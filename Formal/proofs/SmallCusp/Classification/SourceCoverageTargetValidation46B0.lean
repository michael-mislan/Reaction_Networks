import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B01

namespace SmallCusp

def sourceCoverageTargetSlice46B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46B00 ++
  sourceCoverageTargetSlice46B01

theorem sourceCoverageTargetSlice46B0_targetConsistent :
    sourceCoverageTargetSlice46B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46B0,
    sourceCoverageTargetSlice46B00_targetConsistent,
    sourceCoverageTargetSlice46B01_targetConsistent]

theorem sourceCoverageTargetSlice46B0_length : sourceCoverageTargetSlice46B0.length = 125 := by
  simp [sourceCoverageTargetSlice46B0,
    sourceCoverageTargetSlice46B00_length,
    sourceCoverageTargetSlice46B01_length]

end SmallCusp
