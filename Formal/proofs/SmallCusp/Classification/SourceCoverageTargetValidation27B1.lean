import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B11

namespace SmallCusp

def sourceCoverageTargetSlice27B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27B10 ++
  sourceCoverageTargetSlice27B11

theorem sourceCoverageTargetSlice27B1_targetConsistent :
    sourceCoverageTargetSlice27B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27B1,
    sourceCoverageTargetSlice27B10_targetConsistent,
    sourceCoverageTargetSlice27B11_targetConsistent]

theorem sourceCoverageTargetSlice27B1_length : sourceCoverageTargetSlice27B1.length = 125 := by
  simp [sourceCoverageTargetSlice27B1,
    sourceCoverageTargetSlice27B10_length,
    sourceCoverageTargetSlice27B11_length]

end SmallCusp
