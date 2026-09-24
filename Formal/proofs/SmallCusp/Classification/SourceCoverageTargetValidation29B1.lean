import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation29B11

namespace SmallCusp

def sourceCoverageTargetSlice29B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice29B10 ++
  sourceCoverageTargetSlice29B11

theorem sourceCoverageTargetSlice29B1_targetConsistent :
    sourceCoverageTargetSlice29B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice29B1,
    sourceCoverageTargetSlice29B10_targetConsistent,
    sourceCoverageTargetSlice29B11_targetConsistent]

theorem sourceCoverageTargetSlice29B1_length : sourceCoverageTargetSlice29B1.length = 125 := by
  simp [sourceCoverageTargetSlice29B1,
    sourceCoverageTargetSlice29B10_length,
    sourceCoverageTargetSlice29B11_length]

end SmallCusp
