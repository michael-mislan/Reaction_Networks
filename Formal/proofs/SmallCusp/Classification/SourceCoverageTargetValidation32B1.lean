import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B11

namespace SmallCusp

def sourceCoverageTargetSlice32B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32B10 ++
  sourceCoverageTargetSlice32B11

theorem sourceCoverageTargetSlice32B1_targetConsistent :
    sourceCoverageTargetSlice32B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32B1,
    sourceCoverageTargetSlice32B10_targetConsistent,
    sourceCoverageTargetSlice32B11_targetConsistent]

theorem sourceCoverageTargetSlice32B1_length : sourceCoverageTargetSlice32B1.length = 125 := by
  simp [sourceCoverageTargetSlice32B1,
    sourceCoverageTargetSlice32B10_length,
    sourceCoverageTargetSlice32B11_length]

end SmallCusp
