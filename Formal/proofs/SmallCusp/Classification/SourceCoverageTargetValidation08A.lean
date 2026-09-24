import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08A1

namespace SmallCusp

def sourceCoverageTargetSlice08A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice08A0 ++
  sourceCoverageTargetSlice08A1

theorem sourceCoverageTargetSlice08A_targetConsistent :
    sourceCoverageTargetSlice08A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice08A,
    sourceCoverageTargetSlice08A0_targetConsistent,
    sourceCoverageTargetSlice08A1_targetConsistent]

theorem sourceCoverageTargetSlice08A_length : sourceCoverageTargetSlice08A.length = 250 := by
  simp [sourceCoverageTargetSlice08A,
    sourceCoverageTargetSlice08A0_length,
    sourceCoverageTargetSlice08A1_length]

end SmallCusp
