import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B11

namespace SmallCusp

def sourceCoverageTargetSlice49B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49B10 ++
  sourceCoverageTargetSlice49B11

theorem sourceCoverageTargetSlice49B1_targetConsistent :
    sourceCoverageTargetSlice49B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49B1,
    sourceCoverageTargetSlice49B10_targetConsistent,
    sourceCoverageTargetSlice49B11_targetConsistent]

theorem sourceCoverageTargetSlice49B1_length : sourceCoverageTargetSlice49B1.length = 125 := by
  simp [sourceCoverageTargetSlice49B1,
    sourceCoverageTargetSlice49B10_length,
    sourceCoverageTargetSlice49B11_length]

end SmallCusp
