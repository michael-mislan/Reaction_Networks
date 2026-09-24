import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A1

namespace SmallCusp

def sourceCoverageTargetSlice34A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34A0 ++
  sourceCoverageTargetSlice34A1

theorem sourceCoverageTargetSlice34A_targetConsistent :
    sourceCoverageTargetSlice34A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34A,
    sourceCoverageTargetSlice34A0_targetConsistent,
    sourceCoverageTargetSlice34A1_targetConsistent]

theorem sourceCoverageTargetSlice34A_length : sourceCoverageTargetSlice34A.length = 250 := by
  simp [sourceCoverageTargetSlice34A,
    sourceCoverageTargetSlice34A0_length,
    sourceCoverageTargetSlice34A1_length]

end SmallCusp
