import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A1

namespace SmallCusp

def sourceCoverageTargetSlice44A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44A0 ++
  sourceCoverageTargetSlice44A1

theorem sourceCoverageTargetSlice44A_targetConsistent :
    sourceCoverageTargetSlice44A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44A,
    sourceCoverageTargetSlice44A0_targetConsistent,
    sourceCoverageTargetSlice44A1_targetConsistent]

theorem sourceCoverageTargetSlice44A_length : sourceCoverageTargetSlice44A.length = 250 := by
  simp [sourceCoverageTargetSlice44A,
    sourceCoverageTargetSlice44A0_length,
    sourceCoverageTargetSlice44A1_length]

end SmallCusp
