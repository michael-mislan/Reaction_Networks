import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A11

namespace SmallCusp

def sourceCoverageTargetSlice58A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58A10 ++
  sourceCoverageTargetSlice58A11

theorem sourceCoverageTargetSlice58A1_targetConsistent :
    sourceCoverageTargetSlice58A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58A1,
    sourceCoverageTargetSlice58A10_targetConsistent,
    sourceCoverageTargetSlice58A11_targetConsistent]

theorem sourceCoverageTargetSlice58A1_length : sourceCoverageTargetSlice58A1.length = 125 := by
  simp [sourceCoverageTargetSlice58A1,
    sourceCoverageTargetSlice58A10_length,
    sourceCoverageTargetSlice58A11_length]

end SmallCusp
