import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B1

namespace SmallCusp

def sourceCoverageTargetSlice42B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42B0 ++
  sourceCoverageTargetSlice42B1

theorem sourceCoverageTargetSlice42B_targetConsistent :
    sourceCoverageTargetSlice42B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42B,
    sourceCoverageTargetSlice42B0_targetConsistent,
    sourceCoverageTargetSlice42B1_targetConsistent]

theorem sourceCoverageTargetSlice42B_length : sourceCoverageTargetSlice42B.length = 250 := by
  simp [sourceCoverageTargetSlice42B,
    sourceCoverageTargetSlice42B0_length,
    sourceCoverageTargetSlice42B1_length]

end SmallCusp
