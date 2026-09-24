import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation49A01

namespace SmallCusp

def sourceCoverageTargetSlice49A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice49A00 ++
  sourceCoverageTargetSlice49A01

theorem sourceCoverageTargetSlice49A0_targetConsistent :
    sourceCoverageTargetSlice49A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice49A0,
    sourceCoverageTargetSlice49A00_targetConsistent,
    sourceCoverageTargetSlice49A01_targetConsistent]

theorem sourceCoverageTargetSlice49A0_length : sourceCoverageTargetSlice49A0.length = 125 := by
  simp [sourceCoverageTargetSlice49A0,
    sourceCoverageTargetSlice49A00_length,
    sourceCoverageTargetSlice49A01_length]

end SmallCusp
