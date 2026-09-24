import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48B11

namespace SmallCusp

def sourceCoverageTargetSlice48B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48B10 ++
  sourceCoverageTargetSlice48B11

theorem sourceCoverageTargetSlice48B1_targetConsistent :
    sourceCoverageTargetSlice48B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48B1,
    sourceCoverageTargetSlice48B10_targetConsistent,
    sourceCoverageTargetSlice48B11_targetConsistent]

theorem sourceCoverageTargetSlice48B1_length : sourceCoverageTargetSlice48B1.length = 125 := by
  simp [sourceCoverageTargetSlice48B1,
    sourceCoverageTargetSlice48B10_length,
    sourceCoverageTargetSlice48B11_length]

end SmallCusp
