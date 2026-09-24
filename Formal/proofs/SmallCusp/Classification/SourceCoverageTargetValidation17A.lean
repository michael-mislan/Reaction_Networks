import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A1

namespace SmallCusp

def sourceCoverageTargetSlice17A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17A0 ++
  sourceCoverageTargetSlice17A1

theorem sourceCoverageTargetSlice17A_targetConsistent :
    sourceCoverageTargetSlice17A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17A,
    sourceCoverageTargetSlice17A0_targetConsistent,
    sourceCoverageTargetSlice17A1_targetConsistent]

theorem sourceCoverageTargetSlice17A_length : sourceCoverageTargetSlice17A.length = 250 := by
  simp [sourceCoverageTargetSlice17A,
    sourceCoverageTargetSlice17A0_length,
    sourceCoverageTargetSlice17A1_length]

end SmallCusp
