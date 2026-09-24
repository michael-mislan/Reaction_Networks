import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B01

namespace SmallCusp

def sourceCoverageTargetSlice48B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48B00 ++
  sourceCoverageTargetSlice48B01

theorem sourceCoverageTargetSlice48B0_targetConsistent :
    sourceCoverageTargetSlice48B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48B0,
    sourceCoverageTargetSlice48B00_targetConsistent,
    sourceCoverageTargetSlice48B01_targetConsistent]

theorem sourceCoverageTargetSlice48B0_length : sourceCoverageTargetSlice48B0.length = 125 := by
  simp [sourceCoverageTargetSlice48B0,
    sourceCoverageTargetSlice48B00_length,
    sourceCoverageTargetSlice48B01_length]

end SmallCusp
