import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A1

namespace SmallCusp

def sourceCoverageTargetSlice45A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45A0 ++
  sourceCoverageTargetSlice45A1

theorem sourceCoverageTargetSlice45A_targetConsistent :
    sourceCoverageTargetSlice45A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45A,
    sourceCoverageTargetSlice45A0_targetConsistent,
    sourceCoverageTargetSlice45A1_targetConsistent]

theorem sourceCoverageTargetSlice45A_length : sourceCoverageTargetSlice45A.length = 250 := by
  simp [sourceCoverageTargetSlice45A,
    sourceCoverageTargetSlice45A0_length,
    sourceCoverageTargetSlice45A1_length]

end SmallCusp
