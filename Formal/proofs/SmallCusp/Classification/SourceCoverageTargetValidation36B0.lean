import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B01

namespace SmallCusp

def sourceCoverageTargetSlice36B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36B00 ++
  sourceCoverageTargetSlice36B01

theorem sourceCoverageTargetSlice36B0_targetConsistent :
    sourceCoverageTargetSlice36B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36B0,
    sourceCoverageTargetSlice36B00_targetConsistent,
    sourceCoverageTargetSlice36B01_targetConsistent]

theorem sourceCoverageTargetSlice36B0_length : sourceCoverageTargetSlice36B0.length = 125 := by
  simp [sourceCoverageTargetSlice36B0,
    sourceCoverageTargetSlice36B00_length,
    sourceCoverageTargetSlice36B01_length]

end SmallCusp
