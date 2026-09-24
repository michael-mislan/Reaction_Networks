import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B1

namespace SmallCusp

def sourceCoverageTargetSlice36B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36B0 ++
  sourceCoverageTargetSlice36B1

theorem sourceCoverageTargetSlice36B_targetConsistent :
    sourceCoverageTargetSlice36B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36B,
    sourceCoverageTargetSlice36B0_targetConsistent,
    sourceCoverageTargetSlice36B1_targetConsistent]

theorem sourceCoverageTargetSlice36B_length : sourceCoverageTargetSlice36B.length = 250 := by
  simp [sourceCoverageTargetSlice36B,
    sourceCoverageTargetSlice36B0_length,
    sourceCoverageTargetSlice36B1_length]

end SmallCusp
