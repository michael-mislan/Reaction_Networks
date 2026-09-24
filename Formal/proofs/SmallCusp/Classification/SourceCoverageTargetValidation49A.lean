import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A1

namespace SmallCusp

def sourceCoverageTargetSlice49A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49A0 ++
  sourceCoverageTargetSlice49A1

theorem sourceCoverageTargetSlice49A_targetConsistent :
    sourceCoverageTargetSlice49A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49A,
    sourceCoverageTargetSlice49A0_targetConsistent,
    sourceCoverageTargetSlice49A1_targetConsistent]

theorem sourceCoverageTargetSlice49A_length : sourceCoverageTargetSlice49A.length = 250 := by
  simp [sourceCoverageTargetSlice49A,
    sourceCoverageTargetSlice49A0_length,
    sourceCoverageTargetSlice49A1_length]

end SmallCusp
