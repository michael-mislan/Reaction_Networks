import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B11

namespace SmallCusp

def sourceCoverageTargetSlice47B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47B10 ++
  sourceCoverageTargetSlice47B11

theorem sourceCoverageTargetSlice47B1_targetConsistent :
    sourceCoverageTargetSlice47B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47B1,
    sourceCoverageTargetSlice47B10_targetConsistent,
    sourceCoverageTargetSlice47B11_targetConsistent]

theorem sourceCoverageTargetSlice47B1_length : sourceCoverageTargetSlice47B1.length = 125 := by
  simp [sourceCoverageTargetSlice47B1,
    sourceCoverageTargetSlice47B10_length,
    sourceCoverageTargetSlice47B11_length]

end SmallCusp
