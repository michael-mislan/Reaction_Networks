import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27A01

namespace SmallCusp

def sourceCoverageTargetSlice27A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27A00 ++
  sourceCoverageTargetSlice27A01

theorem sourceCoverageTargetSlice27A0_targetConsistent :
    sourceCoverageTargetSlice27A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27A0,
    sourceCoverageTargetSlice27A00_targetConsistent,
    sourceCoverageTargetSlice27A01_targetConsistent]

theorem sourceCoverageTargetSlice27A0_length : sourceCoverageTargetSlice27A0.length = 125 := by
  simp [sourceCoverageTargetSlice27A0,
    sourceCoverageTargetSlice27A00_length,
    sourceCoverageTargetSlice27A01_length]

end SmallCusp
