import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B01

namespace SmallCusp

def sourceCoverageTargetSlice15B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15B00 ++
  sourceCoverageTargetSlice15B01

theorem sourceCoverageTargetSlice15B0_targetConsistent :
    sourceCoverageTargetSlice15B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15B0,
    sourceCoverageTargetSlice15B00_targetConsistent,
    sourceCoverageTargetSlice15B01_targetConsistent]

theorem sourceCoverageTargetSlice15B0_length : sourceCoverageTargetSlice15B0.length = 125 := by
  simp [sourceCoverageTargetSlice15B0,
    sourceCoverageTargetSlice15B00_length,
    sourceCoverageTargetSlice15B01_length]

end SmallCusp
