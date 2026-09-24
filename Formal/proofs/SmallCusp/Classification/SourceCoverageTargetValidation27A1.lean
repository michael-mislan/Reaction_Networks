import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A11

namespace SmallCusp

def sourceCoverageTargetSlice27A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27A10 ++
  sourceCoverageTargetSlice27A11

theorem sourceCoverageTargetSlice27A1_targetConsistent :
    sourceCoverageTargetSlice27A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27A1,
    sourceCoverageTargetSlice27A10_targetConsistent,
    sourceCoverageTargetSlice27A11_targetConsistent]

theorem sourceCoverageTargetSlice27A1_length : sourceCoverageTargetSlice27A1.length = 125 := by
  simp [sourceCoverageTargetSlice27A1,
    sourceCoverageTargetSlice27A10_length,
    sourceCoverageTargetSlice27A11_length]

end SmallCusp
