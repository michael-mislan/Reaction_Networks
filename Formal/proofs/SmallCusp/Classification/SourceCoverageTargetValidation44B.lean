import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B1

namespace SmallCusp

def sourceCoverageTargetSlice44B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44B0 ++
  sourceCoverageTargetSlice44B1

theorem sourceCoverageTargetSlice44B_targetConsistent :
    sourceCoverageTargetSlice44B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44B,
    sourceCoverageTargetSlice44B0_targetConsistent,
    sourceCoverageTargetSlice44B1_targetConsistent]

theorem sourceCoverageTargetSlice44B_length : sourceCoverageTargetSlice44B.length = 250 := by
  simp [sourceCoverageTargetSlice44B,
    sourceCoverageTargetSlice44B0_length,
    sourceCoverageTargetSlice44B1_length]

end SmallCusp
