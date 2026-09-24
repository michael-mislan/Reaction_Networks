import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B1

namespace SmallCusp

def sourceCoverageTargetSlice54B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54B0 ++
  sourceCoverageTargetSlice54B1

theorem sourceCoverageTargetSlice54B_targetConsistent :
    sourceCoverageTargetSlice54B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54B,
    sourceCoverageTargetSlice54B0_targetConsistent,
    sourceCoverageTargetSlice54B1_targetConsistent]

theorem sourceCoverageTargetSlice54B_length : sourceCoverageTargetSlice54B.length = 250 := by
  simp [sourceCoverageTargetSlice54B,
    sourceCoverageTargetSlice54B0_length,
    sourceCoverageTargetSlice54B1_length]

end SmallCusp
