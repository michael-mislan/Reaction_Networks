import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B11

namespace SmallCusp

def sourceCoverageTargetSlice42B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42B10 ++
  sourceCoverageTargetSlice42B11

theorem sourceCoverageTargetSlice42B1_targetConsistent :
    sourceCoverageTargetSlice42B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42B1,
    sourceCoverageTargetSlice42B10_targetConsistent,
    sourceCoverageTargetSlice42B11_targetConsistent]

theorem sourceCoverageTargetSlice42B1_length : sourceCoverageTargetSlice42B1.length = 125 := by
  simp [sourceCoverageTargetSlice42B1,
    sourceCoverageTargetSlice42B10_length,
    sourceCoverageTargetSlice42B11_length]

end SmallCusp
