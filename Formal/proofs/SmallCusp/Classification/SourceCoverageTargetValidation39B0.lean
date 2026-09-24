import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B01

namespace SmallCusp

def sourceCoverageTargetSlice39B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39B00 ++
  sourceCoverageTargetSlice39B01

theorem sourceCoverageTargetSlice39B0_targetConsistent :
    sourceCoverageTargetSlice39B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39B0,
    sourceCoverageTargetSlice39B00_targetConsistent,
    sourceCoverageTargetSlice39B01_targetConsistent]

theorem sourceCoverageTargetSlice39B0_length : sourceCoverageTargetSlice39B0.length = 125 := by
  simp [sourceCoverageTargetSlice39B0,
    sourceCoverageTargetSlice39B00_length,
    sourceCoverageTargetSlice39B01_length]

end SmallCusp
