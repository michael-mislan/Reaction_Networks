import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A1

namespace SmallCusp

def sourceCoverageTargetSlice52A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52A0 ++
  sourceCoverageTargetSlice52A1

theorem sourceCoverageTargetSlice52A_targetConsistent :
    sourceCoverageTargetSlice52A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52A,
    sourceCoverageTargetSlice52A0_targetConsistent,
    sourceCoverageTargetSlice52A1_targetConsistent]

theorem sourceCoverageTargetSlice52A_length : sourceCoverageTargetSlice52A.length = 250 := by
  simp [sourceCoverageTargetSlice52A,
    sourceCoverageTargetSlice52A0_length,
    sourceCoverageTargetSlice52A1_length]

end SmallCusp
