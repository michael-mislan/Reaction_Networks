import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B1

namespace SmallCusp

def sourceCoverageTargetSlice33B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33B0 ++
  sourceCoverageTargetSlice33B1

theorem sourceCoverageTargetSlice33B_targetConsistent :
    sourceCoverageTargetSlice33B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33B,
    sourceCoverageTargetSlice33B0_targetConsistent,
    sourceCoverageTargetSlice33B1_targetConsistent]

theorem sourceCoverageTargetSlice33B_length : sourceCoverageTargetSlice33B.length = 250 := by
  simp [sourceCoverageTargetSlice33B,
    sourceCoverageTargetSlice33B0_length,
    sourceCoverageTargetSlice33B1_length]

end SmallCusp
