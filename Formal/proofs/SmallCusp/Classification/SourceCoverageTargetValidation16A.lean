import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A1

namespace SmallCusp

def sourceCoverageTargetSlice16A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16A0 ++
  sourceCoverageTargetSlice16A1

theorem sourceCoverageTargetSlice16A_targetConsistent :
    sourceCoverageTargetSlice16A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16A,
    sourceCoverageTargetSlice16A0_targetConsistent,
    sourceCoverageTargetSlice16A1_targetConsistent]

theorem sourceCoverageTargetSlice16A_length : sourceCoverageTargetSlice16A.length = 250 := by
  simp [sourceCoverageTargetSlice16A,
    sourceCoverageTargetSlice16A0_length,
    sourceCoverageTargetSlice16A1_length]

end SmallCusp
