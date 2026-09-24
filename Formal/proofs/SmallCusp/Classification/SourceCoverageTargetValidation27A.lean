import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A1

namespace SmallCusp

def sourceCoverageTargetSlice27A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27A0 ++
  sourceCoverageTargetSlice27A1

theorem sourceCoverageTargetSlice27A_targetConsistent :
    sourceCoverageTargetSlice27A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27A,
    sourceCoverageTargetSlice27A0_targetConsistent,
    sourceCoverageTargetSlice27A1_targetConsistent]

theorem sourceCoverageTargetSlice27A_length : sourceCoverageTargetSlice27A.length = 250 := by
  simp [sourceCoverageTargetSlice27A,
    sourceCoverageTargetSlice27A0_length,
    sourceCoverageTargetSlice27A1_length]

end SmallCusp
