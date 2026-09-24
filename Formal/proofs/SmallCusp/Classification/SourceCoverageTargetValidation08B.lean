import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation08B1

namespace SmallCusp

def sourceCoverageTargetSlice08B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice08B0 ++
  sourceCoverageTargetSlice08B1

theorem sourceCoverageTargetSlice08B_targetConsistent :
    sourceCoverageTargetSlice08B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice08B,
    sourceCoverageTargetSlice08B0_targetConsistent,
    sourceCoverageTargetSlice08B1_targetConsistent]

theorem sourceCoverageTargetSlice08B_length : sourceCoverageTargetSlice08B.length = 250 := by
  simp [sourceCoverageTargetSlice08B,
    sourceCoverageTargetSlice08B0_length,
    sourceCoverageTargetSlice08B1_length]

end SmallCusp
