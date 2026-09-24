import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52B01

namespace SmallCusp

def sourceCoverageTargetSlice52B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52B00 ++
  sourceCoverageTargetSlice52B01

theorem sourceCoverageTargetSlice52B0_targetConsistent :
    sourceCoverageTargetSlice52B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52B0,
    sourceCoverageTargetSlice52B00_targetConsistent,
    sourceCoverageTargetSlice52B01_targetConsistent]

theorem sourceCoverageTargetSlice52B0_length : sourceCoverageTargetSlice52B0.length = 125 := by
  simp [sourceCoverageTargetSlice52B0,
    sourceCoverageTargetSlice52B00_length,
    sourceCoverageTargetSlice52B01_length]

end SmallCusp
