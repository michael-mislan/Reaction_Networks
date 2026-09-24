import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B11

namespace SmallCusp

def sourceCoverageTargetSlice52B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52B10 ++
  sourceCoverageTargetSlice52B11

theorem sourceCoverageTargetSlice52B1_targetConsistent :
    sourceCoverageTargetSlice52B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52B1,
    sourceCoverageTargetSlice52B10_targetConsistent,
    sourceCoverageTargetSlice52B11_targetConsistent]

theorem sourceCoverageTargetSlice52B1_length : sourceCoverageTargetSlice52B1.length = 125 := by
  simp [sourceCoverageTargetSlice52B1,
    sourceCoverageTargetSlice52B10_length,
    sourceCoverageTargetSlice52B11_length]

end SmallCusp
