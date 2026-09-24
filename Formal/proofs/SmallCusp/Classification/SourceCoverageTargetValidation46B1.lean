import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46B11

namespace SmallCusp

def sourceCoverageTargetSlice46B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46B10 ++
  sourceCoverageTargetSlice46B11

theorem sourceCoverageTargetSlice46B1_targetConsistent :
    sourceCoverageTargetSlice46B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46B1,
    sourceCoverageTargetSlice46B10_targetConsistent,
    sourceCoverageTargetSlice46B11_targetConsistent]

theorem sourceCoverageTargetSlice46B1_length : sourceCoverageTargetSlice46B1.length = 125 := by
  simp [sourceCoverageTargetSlice46B1,
    sourceCoverageTargetSlice46B10_length,
    sourceCoverageTargetSlice46B11_length]

end SmallCusp
