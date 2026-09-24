import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A1

namespace SmallCusp

def sourceCoverageTargetSlice58A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58A0 ++
  sourceCoverageTargetSlice58A1

theorem sourceCoverageTargetSlice58A_targetConsistent :
    sourceCoverageTargetSlice58A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58A,
    sourceCoverageTargetSlice58A0_targetConsistent,
    sourceCoverageTargetSlice58A1_targetConsistent]

theorem sourceCoverageTargetSlice58A_length : sourceCoverageTargetSlice58A.length = 250 := by
  simp [sourceCoverageTargetSlice58A,
    sourceCoverageTargetSlice58A0_length,
    sourceCoverageTargetSlice58A1_length]

end SmallCusp
