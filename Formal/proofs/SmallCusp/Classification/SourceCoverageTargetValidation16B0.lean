import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B01

namespace SmallCusp

def sourceCoverageTargetSlice16B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16B00 ++
  sourceCoverageTargetSlice16B01

theorem sourceCoverageTargetSlice16B0_targetConsistent :
    sourceCoverageTargetSlice16B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16B0,
    sourceCoverageTargetSlice16B00_targetConsistent,
    sourceCoverageTargetSlice16B01_targetConsistent]

theorem sourceCoverageTargetSlice16B0_length : sourceCoverageTargetSlice16B0.length = 125 := by
  simp [sourceCoverageTargetSlice16B0,
    sourceCoverageTargetSlice16B00_length,
    sourceCoverageTargetSlice16B01_length]

end SmallCusp
