import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42B01

namespace SmallCusp

def sourceCoverageTargetSlice42B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42B00 ++
  sourceCoverageTargetSlice42B01

theorem sourceCoverageTargetSlice42B0_targetConsistent :
    sourceCoverageTargetSlice42B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42B0,
    sourceCoverageTargetSlice42B00_targetConsistent,
    sourceCoverageTargetSlice42B01_targetConsistent]

theorem sourceCoverageTargetSlice42B0_length : sourceCoverageTargetSlice42B0.length = 125 := by
  simp [sourceCoverageTargetSlice42B0,
    sourceCoverageTargetSlice42B00_length,
    sourceCoverageTargetSlice42B01_length]

end SmallCusp
