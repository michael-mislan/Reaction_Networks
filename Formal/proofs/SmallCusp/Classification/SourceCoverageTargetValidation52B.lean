import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B1

namespace SmallCusp

def sourceCoverageTargetSlice52B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52B0 ++
  sourceCoverageTargetSlice52B1

theorem sourceCoverageTargetSlice52B_targetConsistent :
    sourceCoverageTargetSlice52B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52B,
    sourceCoverageTargetSlice52B0_targetConsistent,
    sourceCoverageTargetSlice52B1_targetConsistent]

theorem sourceCoverageTargetSlice52B_length : sourceCoverageTargetSlice52B.length = 250 := by
  simp [sourceCoverageTargetSlice52B,
    sourceCoverageTargetSlice52B0_length,
    sourceCoverageTargetSlice52B1_length]

end SmallCusp
