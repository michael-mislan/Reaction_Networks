import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A1

namespace SmallCusp

def sourceCoverageTargetSlice23A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23A0 ++
  sourceCoverageTargetSlice23A1

theorem sourceCoverageTargetSlice23A_targetConsistent :
    sourceCoverageTargetSlice23A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23A,
    sourceCoverageTargetSlice23A0_targetConsistent,
    sourceCoverageTargetSlice23A1_targetConsistent]

theorem sourceCoverageTargetSlice23A_length : sourceCoverageTargetSlice23A.length = 250 := by
  simp [sourceCoverageTargetSlice23A,
    sourceCoverageTargetSlice23A0_length,
    sourceCoverageTargetSlice23A1_length]

end SmallCusp
