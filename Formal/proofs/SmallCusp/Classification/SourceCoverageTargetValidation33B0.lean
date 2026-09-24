import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33B01

namespace SmallCusp

def sourceCoverageTargetSlice33B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33B00 ++
  sourceCoverageTargetSlice33B01

theorem sourceCoverageTargetSlice33B0_targetConsistent :
    sourceCoverageTargetSlice33B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33B0,
    sourceCoverageTargetSlice33B00_targetConsistent,
    sourceCoverageTargetSlice33B01_targetConsistent]

theorem sourceCoverageTargetSlice33B0_length : sourceCoverageTargetSlice33B0.length = 125 := by
  simp [sourceCoverageTargetSlice33B0,
    sourceCoverageTargetSlice33B00_length,
    sourceCoverageTargetSlice33B01_length]

end SmallCusp
