import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A11

namespace SmallCusp

def sourceCoverageTargetSlice37A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37A10 ++
  sourceCoverageTargetSlice37A11

theorem sourceCoverageTargetSlice37A1_targetConsistent :
    sourceCoverageTargetSlice37A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37A1,
    sourceCoverageTargetSlice37A10_targetConsistent,
    sourceCoverageTargetSlice37A11_targetConsistent]

theorem sourceCoverageTargetSlice37A1_length : sourceCoverageTargetSlice37A1.length = 125 := by
  simp [sourceCoverageTargetSlice37A1,
    sourceCoverageTargetSlice37A10_length,
    sourceCoverageTargetSlice37A11_length]

end SmallCusp
