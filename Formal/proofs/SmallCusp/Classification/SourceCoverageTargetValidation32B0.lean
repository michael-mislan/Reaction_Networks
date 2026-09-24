import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32B01

namespace SmallCusp

def sourceCoverageTargetSlice32B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32B00 ++
  sourceCoverageTargetSlice32B01

theorem sourceCoverageTargetSlice32B0_targetConsistent :
    sourceCoverageTargetSlice32B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32B0,
    sourceCoverageTargetSlice32B00_targetConsistent,
    sourceCoverageTargetSlice32B01_targetConsistent]

theorem sourceCoverageTargetSlice32B0_length : sourceCoverageTargetSlice32B0.length = 125 := by
  simp [sourceCoverageTargetSlice32B0,
    sourceCoverageTargetSlice32B00_length,
    sourceCoverageTargetSlice32B01_length]

end SmallCusp
