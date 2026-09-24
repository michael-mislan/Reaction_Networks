import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B1

namespace SmallCusp

def sourceCoverageTargetSlice47B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47B0 ++
  sourceCoverageTargetSlice47B1

theorem sourceCoverageTargetSlice47B_targetConsistent :
    sourceCoverageTargetSlice47B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47B,
    sourceCoverageTargetSlice47B0_targetConsistent,
    sourceCoverageTargetSlice47B1_targetConsistent]

theorem sourceCoverageTargetSlice47B_length : sourceCoverageTargetSlice47B.length = 250 := by
  simp [sourceCoverageTargetSlice47B,
    sourceCoverageTargetSlice47B0_length,
    sourceCoverageTargetSlice47B1_length]

end SmallCusp
