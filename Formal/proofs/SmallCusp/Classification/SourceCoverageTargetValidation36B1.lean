import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36B11

namespace SmallCusp

def sourceCoverageTargetSlice36B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36B10 ++
  sourceCoverageTargetSlice36B11

theorem sourceCoverageTargetSlice36B1_targetConsistent :
    sourceCoverageTargetSlice36B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36B1,
    sourceCoverageTargetSlice36B10_targetConsistent,
    sourceCoverageTargetSlice36B11_targetConsistent]

theorem sourceCoverageTargetSlice36B1_length : sourceCoverageTargetSlice36B1.length = 125 := by
  simp [sourceCoverageTargetSlice36B1,
    sourceCoverageTargetSlice36B10_length,
    sourceCoverageTargetSlice36B11_length]

end SmallCusp
