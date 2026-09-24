import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B01

namespace SmallCusp

def sourceCoverageTargetSlice29B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29B00 ++
  sourceCoverageTargetSlice29B01

theorem sourceCoverageTargetSlice29B0_targetConsistent :
    sourceCoverageTargetSlice29B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29B0,
    sourceCoverageTargetSlice29B00_targetConsistent,
    sourceCoverageTargetSlice29B01_targetConsistent]

theorem sourceCoverageTargetSlice29B0_length : sourceCoverageTargetSlice29B0.length = 125 := by
  simp [sourceCoverageTargetSlice29B0,
    sourceCoverageTargetSlice29B00_length,
    sourceCoverageTargetSlice29B01_length]

end SmallCusp
