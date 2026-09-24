import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A11

namespace SmallCusp

def sourceCoverageTargetSlice16A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16A10 ++
  sourceCoverageTargetSlice16A11

theorem sourceCoverageTargetSlice16A1_targetConsistent :
    sourceCoverageTargetSlice16A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16A1,
    sourceCoverageTargetSlice16A10_targetConsistent,
    sourceCoverageTargetSlice16A11_targetConsistent]

theorem sourceCoverageTargetSlice16A1_length : sourceCoverageTargetSlice16A1.length = 125 := by
  simp [sourceCoverageTargetSlice16A1,
    sourceCoverageTargetSlice16A10_length,
    sourceCoverageTargetSlice16A11_length]

end SmallCusp
