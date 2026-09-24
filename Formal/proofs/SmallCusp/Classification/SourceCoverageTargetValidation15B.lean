import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B1

namespace SmallCusp

def sourceCoverageTargetSlice15B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15B0 ++
  sourceCoverageTargetSlice15B1

theorem sourceCoverageTargetSlice15B_targetConsistent :
    sourceCoverageTargetSlice15B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15B,
    sourceCoverageTargetSlice15B0_targetConsistent,
    sourceCoverageTargetSlice15B1_targetConsistent]

theorem sourceCoverageTargetSlice15B_length : sourceCoverageTargetSlice15B.length = 250 := by
  simp [sourceCoverageTargetSlice15B,
    sourceCoverageTargetSlice15B0_length,
    sourceCoverageTargetSlice15B1_length]

end SmallCusp
