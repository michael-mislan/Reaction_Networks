import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B01

namespace SmallCusp

def sourceCoverageTargetSlice44B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44B00 ++
  sourceCoverageTargetSlice44B01

theorem sourceCoverageTargetSlice44B0_targetConsistent :
    sourceCoverageTargetSlice44B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44B0,
    sourceCoverageTargetSlice44B00_targetConsistent,
    sourceCoverageTargetSlice44B01_targetConsistent]

theorem sourceCoverageTargetSlice44B0_length : sourceCoverageTargetSlice44B0.length = 125 := by
  simp [sourceCoverageTargetSlice44B0,
    sourceCoverageTargetSlice44B00_length,
    sourceCoverageTargetSlice44B01_length]

end SmallCusp
