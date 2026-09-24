import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B11

namespace SmallCusp

def sourceCoverageTargetSlice16B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16B10 ++
  sourceCoverageTargetSlice16B11

theorem sourceCoverageTargetSlice16B1_targetConsistent :
    sourceCoverageTargetSlice16B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16B1,
    sourceCoverageTargetSlice16B10_targetConsistent,
    sourceCoverageTargetSlice16B11_targetConsistent]

theorem sourceCoverageTargetSlice16B1_length : sourceCoverageTargetSlice16B1.length = 125 := by
  simp [sourceCoverageTargetSlice16B1,
    sourceCoverageTargetSlice16B10_length,
    sourceCoverageTargetSlice16B11_length]

end SmallCusp
