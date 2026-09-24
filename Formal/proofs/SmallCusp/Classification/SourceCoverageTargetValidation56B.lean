import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B1

namespace SmallCusp

def sourceCoverageTargetSlice56B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56B0 ++
  sourceCoverageTargetSlice56B1

theorem sourceCoverageTargetSlice56B_targetConsistent :
    sourceCoverageTargetSlice56B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56B,
    sourceCoverageTargetSlice56B0_targetConsistent,
    sourceCoverageTargetSlice56B1_targetConsistent]

theorem sourceCoverageTargetSlice56B_length : sourceCoverageTargetSlice56B.length = 250 := by
  simp [sourceCoverageTargetSlice56B,
    sourceCoverageTargetSlice56B0_length,
    sourceCoverageTargetSlice56B1_length]

end SmallCusp
