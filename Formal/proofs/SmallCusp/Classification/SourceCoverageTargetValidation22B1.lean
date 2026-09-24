import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B11

namespace SmallCusp

def sourceCoverageTargetSlice22B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22B10 ++
  sourceCoverageTargetSlice22B11

theorem sourceCoverageTargetSlice22B1_targetConsistent :
    sourceCoverageTargetSlice22B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22B1,
    sourceCoverageTargetSlice22B10_targetConsistent,
    sourceCoverageTargetSlice22B11_targetConsistent]

theorem sourceCoverageTargetSlice22B1_length : sourceCoverageTargetSlice22B1.length = 125 := by
  simp [sourceCoverageTargetSlice22B1,
    sourceCoverageTargetSlice22B10_length,
    sourceCoverageTargetSlice22B11_length]

end SmallCusp
