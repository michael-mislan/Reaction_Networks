import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A1

namespace SmallCusp

def sourceCoverageTargetSlice37A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37A0 ++
  sourceCoverageTargetSlice37A1

theorem sourceCoverageTargetSlice37A_targetConsistent :
    sourceCoverageTargetSlice37A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37A,
    sourceCoverageTargetSlice37A0_targetConsistent,
    sourceCoverageTargetSlice37A1_targetConsistent]

theorem sourceCoverageTargetSlice37A_length : sourceCoverageTargetSlice37A.length = 250 := by
  simp [sourceCoverageTargetSlice37A,
    sourceCoverageTargetSlice37A0_length,
    sourceCoverageTargetSlice37A1_length]

end SmallCusp
