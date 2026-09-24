import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44B11

namespace SmallCusp

def sourceCoverageTargetSlice44B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44B10 ++
  sourceCoverageTargetSlice44B11

theorem sourceCoverageTargetSlice44B1_targetConsistent :
    sourceCoverageTargetSlice44B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44B1,
    sourceCoverageTargetSlice44B10_targetConsistent,
    sourceCoverageTargetSlice44B11_targetConsistent]

theorem sourceCoverageTargetSlice44B1_length : sourceCoverageTargetSlice44B1.length = 125 := by
  simp [sourceCoverageTargetSlice44B1,
    sourceCoverageTargetSlice44B10_length,
    sourceCoverageTargetSlice44B11_length]

end SmallCusp
