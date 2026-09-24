import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B11

namespace SmallCusp

def sourceCoverageTargetSlice54B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54B10 ++
  sourceCoverageTargetSlice54B11

theorem sourceCoverageTargetSlice54B1_targetConsistent :
    sourceCoverageTargetSlice54B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54B1,
    sourceCoverageTargetSlice54B10_targetConsistent,
    sourceCoverageTargetSlice54B11_targetConsistent]

theorem sourceCoverageTargetSlice54B1_length : sourceCoverageTargetSlice54B1.length = 125 := by
  simp [sourceCoverageTargetSlice54B1,
    sourceCoverageTargetSlice54B10_length,
    sourceCoverageTargetSlice54B11_length]

end SmallCusp
