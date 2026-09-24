import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14A1

namespace SmallCusp

def sourceCoverageTargetSlice14A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice14A0 ++
  sourceCoverageTargetSlice14A1

theorem sourceCoverageTargetSlice14A_targetConsistent :
    sourceCoverageTargetSlice14A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice14A,
    sourceCoverageTargetSlice14A0_targetConsistent,
    sourceCoverageTargetSlice14A1_targetConsistent]

theorem sourceCoverageTargetSlice14A_length : sourceCoverageTargetSlice14A.length = 250 := by
  simp [sourceCoverageTargetSlice14A,
    sourceCoverageTargetSlice14A0_length,
    sourceCoverageTargetSlice14A1_length]

end SmallCusp
