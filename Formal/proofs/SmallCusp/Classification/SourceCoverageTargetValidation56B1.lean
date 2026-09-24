import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B11

namespace SmallCusp

def sourceCoverageTargetSlice56B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56B10 ++
  sourceCoverageTargetSlice56B11

theorem sourceCoverageTargetSlice56B1_targetConsistent :
    sourceCoverageTargetSlice56B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56B1,
    sourceCoverageTargetSlice56B10_targetConsistent,
    sourceCoverageTargetSlice56B11_targetConsistent]

theorem sourceCoverageTargetSlice56B1_length : sourceCoverageTargetSlice56B1.length = 125 := by
  simp [sourceCoverageTargetSlice56B1,
    sourceCoverageTargetSlice56B10_length,
    sourceCoverageTargetSlice56B11_length]

end SmallCusp
