import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A11

namespace SmallCusp

def sourceCoverageTargetSlice52A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52A10 ++
  sourceCoverageTargetSlice52A11

theorem sourceCoverageTargetSlice52A1_targetConsistent :
    sourceCoverageTargetSlice52A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52A1,
    sourceCoverageTargetSlice52A10_targetConsistent,
    sourceCoverageTargetSlice52A11_targetConsistent]

theorem sourceCoverageTargetSlice52A1_length : sourceCoverageTargetSlice52A1.length = 125 := by
  simp [sourceCoverageTargetSlice52A1,
    sourceCoverageTargetSlice52A10_length,
    sourceCoverageTargetSlice52A11_length]

end SmallCusp
