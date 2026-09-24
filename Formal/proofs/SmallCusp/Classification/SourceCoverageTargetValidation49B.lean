import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49B1

namespace SmallCusp

def sourceCoverageTargetSlice49B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49B0 ++
  sourceCoverageTargetSlice49B1

theorem sourceCoverageTargetSlice49B_targetConsistent :
    sourceCoverageTargetSlice49B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49B,
    sourceCoverageTargetSlice49B0_targetConsistent,
    sourceCoverageTargetSlice49B1_targetConsistent]

theorem sourceCoverageTargetSlice49B_length : sourceCoverageTargetSlice49B.length = 250 := by
  simp [sourceCoverageTargetSlice49B,
    sourceCoverageTargetSlice49B0_length,
    sourceCoverageTargetSlice49B1_length]

end SmallCusp
