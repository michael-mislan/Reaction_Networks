import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47B01

namespace SmallCusp

def sourceCoverageTargetSlice47B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47B00 ++
  sourceCoverageTargetSlice47B01

theorem sourceCoverageTargetSlice47B0_targetConsistent :
    sourceCoverageTargetSlice47B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47B0,
    sourceCoverageTargetSlice47B00_targetConsistent,
    sourceCoverageTargetSlice47B01_targetConsistent]

theorem sourceCoverageTargetSlice47B0_length : sourceCoverageTargetSlice47B0.length = 125 := by
  simp [sourceCoverageTargetSlice47B0,
    sourceCoverageTargetSlice47B00_length,
    sourceCoverageTargetSlice47B01_length]

end SmallCusp
