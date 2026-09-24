import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B01

namespace SmallCusp

def sourceCoverageTargetSlice37B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37B00 ++
  sourceCoverageTargetSlice37B01

theorem sourceCoverageTargetSlice37B0_targetConsistent :
    sourceCoverageTargetSlice37B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37B0,
    sourceCoverageTargetSlice37B00_targetConsistent,
    sourceCoverageTargetSlice37B01_targetConsistent]

theorem sourceCoverageTargetSlice37B0_length : sourceCoverageTargetSlice37B0.length = 125 := by
  simp [sourceCoverageTargetSlice37B0,
    sourceCoverageTargetSlice37B00_length,
    sourceCoverageTargetSlice37B01_length]

end SmallCusp
