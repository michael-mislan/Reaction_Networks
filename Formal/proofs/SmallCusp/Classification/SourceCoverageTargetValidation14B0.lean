import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B01

namespace SmallCusp

def sourceCoverageTargetSlice14B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice14B00 ++
  sourceCoverageTargetSlice14B01

theorem sourceCoverageTargetSlice14B0_targetConsistent :
    sourceCoverageTargetSlice14B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice14B0,
    sourceCoverageTargetSlice14B00_targetConsistent,
    sourceCoverageTargetSlice14B01_targetConsistent]

theorem sourceCoverageTargetSlice14B0_length : sourceCoverageTargetSlice14B0.length = 125 := by
  simp [sourceCoverageTargetSlice14B0,
    sourceCoverageTargetSlice14B00_length,
    sourceCoverageTargetSlice14B01_length]

end SmallCusp
