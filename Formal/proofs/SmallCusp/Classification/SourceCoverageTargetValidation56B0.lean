import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56B01

namespace SmallCusp

def sourceCoverageTargetSlice56B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56B00 ++
  sourceCoverageTargetSlice56B01

theorem sourceCoverageTargetSlice56B0_targetConsistent :
    sourceCoverageTargetSlice56B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56B0,
    sourceCoverageTargetSlice56B00_targetConsistent,
    sourceCoverageTargetSlice56B01_targetConsistent]

theorem sourceCoverageTargetSlice56B0_length : sourceCoverageTargetSlice56B0.length = 125 := by
  simp [sourceCoverageTargetSlice56B0,
    sourceCoverageTargetSlice56B00_length,
    sourceCoverageTargetSlice56B01_length]

end SmallCusp
