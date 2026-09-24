import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B11

namespace SmallCusp

def sourceCoverageTargetSlice33B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33B10 ++
  sourceCoverageTargetSlice33B11

theorem sourceCoverageTargetSlice33B1_targetConsistent :
    sourceCoverageTargetSlice33B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33B1,
    sourceCoverageTargetSlice33B10_targetConsistent,
    sourceCoverageTargetSlice33B11_targetConsistent]

theorem sourceCoverageTargetSlice33B1_length : sourceCoverageTargetSlice33B1.length = 125 := by
  simp [sourceCoverageTargetSlice33B1,
    sourceCoverageTargetSlice33B10_length,
    sourceCoverageTargetSlice33B11_length]

end SmallCusp
