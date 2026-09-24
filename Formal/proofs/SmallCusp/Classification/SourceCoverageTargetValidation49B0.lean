import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B01

namespace SmallCusp

def sourceCoverageTargetSlice49B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49B00 ++
  sourceCoverageTargetSlice49B01

theorem sourceCoverageTargetSlice49B0_targetConsistent :
    sourceCoverageTargetSlice49B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49B0,
    sourceCoverageTargetSlice49B00_targetConsistent,
    sourceCoverageTargetSlice49B01_targetConsistent]

theorem sourceCoverageTargetSlice49B0_length : sourceCoverageTargetSlice49B0.length = 125 := by
  simp [sourceCoverageTargetSlice49B0,
    sourceCoverageTargetSlice49B00_length,
    sourceCoverageTargetSlice49B01_length]

end SmallCusp
