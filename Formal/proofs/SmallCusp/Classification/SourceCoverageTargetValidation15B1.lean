import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15B11

namespace SmallCusp

def sourceCoverageTargetSlice15B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15B10 ++
  sourceCoverageTargetSlice15B11

theorem sourceCoverageTargetSlice15B1_targetConsistent :
    sourceCoverageTargetSlice15B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15B1,
    sourceCoverageTargetSlice15B10_targetConsistent,
    sourceCoverageTargetSlice15B11_targetConsistent]

theorem sourceCoverageTargetSlice15B1_length : sourceCoverageTargetSlice15B1.length = 125 := by
  simp [sourceCoverageTargetSlice15B1,
    sourceCoverageTargetSlice15B10_length,
    sourceCoverageTargetSlice15B11_length]

end SmallCusp
