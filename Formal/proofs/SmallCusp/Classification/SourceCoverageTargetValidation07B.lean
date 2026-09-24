import proofs.SmallCusp.Classification.SourceCoverageTargetValidation07B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation07B1

namespace SmallCusp

def sourceCoverageTargetSlice07B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice07B0 ++
  sourceCoverageTargetSlice07B1

theorem sourceCoverageTargetSlice07B_targetConsistent :
    sourceCoverageTargetSlice07B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice07B,
    sourceCoverageTargetSlice07B0_targetConsistent,
    sourceCoverageTargetSlice07B1_targetConsistent]

theorem sourceCoverageTargetSlice07B_length : sourceCoverageTargetSlice07B.length = 250 := by
  simp [sourceCoverageTargetSlice07B,
    sourceCoverageTargetSlice07B0_length,
    sourceCoverageTargetSlice07B1_length]

end SmallCusp
