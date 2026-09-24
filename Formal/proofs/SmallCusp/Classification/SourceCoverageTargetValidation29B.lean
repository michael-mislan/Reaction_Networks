import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B1

namespace SmallCusp

def sourceCoverageTargetSlice29B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29B0 ++
  sourceCoverageTargetSlice29B1

theorem sourceCoverageTargetSlice29B_targetConsistent :
    sourceCoverageTargetSlice29B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29B,
    sourceCoverageTargetSlice29B0_targetConsistent,
    sourceCoverageTargetSlice29B1_targetConsistent]

theorem sourceCoverageTargetSlice29B_length : sourceCoverageTargetSlice29B.length = 250 := by
  simp [sourceCoverageTargetSlice29B,
    sourceCoverageTargetSlice29B0_length,
    sourceCoverageTargetSlice29B1_length]

end SmallCusp
