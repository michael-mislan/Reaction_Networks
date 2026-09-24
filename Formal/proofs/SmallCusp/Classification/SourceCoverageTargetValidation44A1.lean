import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A11

namespace SmallCusp

def sourceCoverageTargetSlice44A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44A10 ++
  sourceCoverageTargetSlice44A11

theorem sourceCoverageTargetSlice44A1_targetConsistent :
    sourceCoverageTargetSlice44A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44A1,
    sourceCoverageTargetSlice44A10_targetConsistent,
    sourceCoverageTargetSlice44A11_targetConsistent]

theorem sourceCoverageTargetSlice44A1_length : sourceCoverageTargetSlice44A1.length = 125 := by
  simp [sourceCoverageTargetSlice44A1,
    sourceCoverageTargetSlice44A10_length,
    sourceCoverageTargetSlice44A11_length]

end SmallCusp
