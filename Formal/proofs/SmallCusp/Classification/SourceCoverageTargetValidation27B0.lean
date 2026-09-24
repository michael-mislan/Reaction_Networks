import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B01

namespace SmallCusp

def sourceCoverageTargetSlice27B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27B00 ++
  sourceCoverageTargetSlice27B01

theorem sourceCoverageTargetSlice27B0_targetConsistent :
    sourceCoverageTargetSlice27B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27B0,
    sourceCoverageTargetSlice27B00_targetConsistent,
    sourceCoverageTargetSlice27B01_targetConsistent]

theorem sourceCoverageTargetSlice27B0_length : sourceCoverageTargetSlice27B0.length = 125 := by
  simp [sourceCoverageTargetSlice27B0,
    sourceCoverageTargetSlice27B00_length,
    sourceCoverageTargetSlice27B01_length]

end SmallCusp
