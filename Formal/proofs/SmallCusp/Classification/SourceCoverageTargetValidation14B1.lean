import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B11

namespace SmallCusp

def sourceCoverageTargetSlice14B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice14B10 ++
  sourceCoverageTargetSlice14B11

theorem sourceCoverageTargetSlice14B1_targetConsistent :
    sourceCoverageTargetSlice14B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice14B1,
    sourceCoverageTargetSlice14B10_targetConsistent,
    sourceCoverageTargetSlice14B11_targetConsistent]

theorem sourceCoverageTargetSlice14B1_length : sourceCoverageTargetSlice14B1.length = 125 := by
  simp [sourceCoverageTargetSlice14B1,
    sourceCoverageTargetSlice14B10_length,
    sourceCoverageTargetSlice14B11_length]

end SmallCusp
