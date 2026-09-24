import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A1

namespace SmallCusp

def sourceCoverageTargetSlice28A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28A0 ++
  sourceCoverageTargetSlice28A1

theorem sourceCoverageTargetSlice28A_targetConsistent :
    sourceCoverageTargetSlice28A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28A,
    sourceCoverageTargetSlice28A0_targetConsistent,
    sourceCoverageTargetSlice28A1_targetConsistent]

theorem sourceCoverageTargetSlice28A_length : sourceCoverageTargetSlice28A.length = 250 := by
  simp [sourceCoverageTargetSlice28A,
    sourceCoverageTargetSlice28A0_length,
    sourceCoverageTargetSlice28A1_length]

end SmallCusp
