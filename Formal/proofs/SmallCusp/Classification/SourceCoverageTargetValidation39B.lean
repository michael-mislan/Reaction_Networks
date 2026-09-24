import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39B1

namespace SmallCusp

def sourceCoverageTargetSlice39B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39B0 ++
  sourceCoverageTargetSlice39B1

theorem sourceCoverageTargetSlice39B_targetConsistent :
    sourceCoverageTargetSlice39B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39B,
    sourceCoverageTargetSlice39B0_targetConsistent,
    sourceCoverageTargetSlice39B1_targetConsistent]

theorem sourceCoverageTargetSlice39B_length : sourceCoverageTargetSlice39B.length = 250 := by
  simp [sourceCoverageTargetSlice39B,
    sourceCoverageTargetSlice39B0_length,
    sourceCoverageTargetSlice39B1_length]

end SmallCusp
