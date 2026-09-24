import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B1

namespace SmallCusp

def sourceCoverageTargetSlice48B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48B0 ++
  sourceCoverageTargetSlice48B1

theorem sourceCoverageTargetSlice48B_targetConsistent :
    sourceCoverageTargetSlice48B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48B,
    sourceCoverageTargetSlice48B0_targetConsistent,
    sourceCoverageTargetSlice48B1_targetConsistent]

theorem sourceCoverageTargetSlice48B_length : sourceCoverageTargetSlice48B.length = 250 := by
  simp [sourceCoverageTargetSlice48B,
    sourceCoverageTargetSlice48B0_length,
    sourceCoverageTargetSlice48B1_length]

end SmallCusp
