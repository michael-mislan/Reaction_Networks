import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation12B1

namespace SmallCusp

def sourceCoverageTargetSlice12B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice12B0 ++
  sourceCoverageTargetSlice12B1

theorem sourceCoverageTargetSlice12B_targetConsistent :
    sourceCoverageTargetSlice12B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice12B,
    sourceCoverageTargetSlice12B0_targetConsistent,
    sourceCoverageTargetSlice12B1_targetConsistent]

theorem sourceCoverageTargetSlice12B_length : sourceCoverageTargetSlice12B.length = 250 := by
  simp [sourceCoverageTargetSlice12B,
    sourceCoverageTargetSlice12B0_length,
    sourceCoverageTargetSlice12B1_length]

end SmallCusp
