import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation27B1

namespace SmallCusp

def sourceCoverageTargetSlice27B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice27B0 ++
  sourceCoverageTargetSlice27B1

theorem sourceCoverageTargetSlice27B_targetConsistent :
    sourceCoverageTargetSlice27B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice27B,
    sourceCoverageTargetSlice27B0_targetConsistent,
    sourceCoverageTargetSlice27B1_targetConsistent]

theorem sourceCoverageTargetSlice27B_length : sourceCoverageTargetSlice27B.length = 250 := by
  simp [sourceCoverageTargetSlice27B,
    sourceCoverageTargetSlice27B0_length,
    sourceCoverageTargetSlice27B1_length]

end SmallCusp
