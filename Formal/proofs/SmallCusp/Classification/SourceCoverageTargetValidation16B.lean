import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16B1

namespace SmallCusp

def sourceCoverageTargetSlice16B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16B0 ++
  sourceCoverageTargetSlice16B1

theorem sourceCoverageTargetSlice16B_targetConsistent :
    sourceCoverageTargetSlice16B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16B,
    sourceCoverageTargetSlice16B0_targetConsistent,
    sourceCoverageTargetSlice16B1_targetConsistent]

theorem sourceCoverageTargetSlice16B_length : sourceCoverageTargetSlice16B.length = 250 := by
  simp [sourceCoverageTargetSlice16B,
    sourceCoverageTargetSlice16B0_length,
    sourceCoverageTargetSlice16B1_length]

end SmallCusp
