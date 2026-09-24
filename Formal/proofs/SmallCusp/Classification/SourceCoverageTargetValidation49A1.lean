import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A11

namespace SmallCusp

def sourceCoverageTargetSlice49A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49A10 ++
  sourceCoverageTargetSlice49A11

theorem sourceCoverageTargetSlice49A1_targetConsistent :
    sourceCoverageTargetSlice49A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49A1,
    sourceCoverageTargetSlice49A10_targetConsistent,
    sourceCoverageTargetSlice49A11_targetConsistent]

theorem sourceCoverageTargetSlice49A1_length : sourceCoverageTargetSlice49A1.length = 125 := by
  simp [sourceCoverageTargetSlice49A1,
    sourceCoverageTargetSlice49A10_length,
    sourceCoverageTargetSlice49A11_length]

end SmallCusp
