import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13B1

namespace SmallCusp

def sourceCoverageTargetSlice13B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice13B0 ++
  sourceCoverageTargetSlice13B1

theorem sourceCoverageTargetSlice13B_targetConsistent :
    sourceCoverageTargetSlice13B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice13B,
    sourceCoverageTargetSlice13B0_targetConsistent,
    sourceCoverageTargetSlice13B1_targetConsistent]

theorem sourceCoverageTargetSlice13B_length : sourceCoverageTargetSlice13B.length = 250 := by
  simp [sourceCoverageTargetSlice13B,
    sourceCoverageTargetSlice13B0_length,
    sourceCoverageTargetSlice13B1_length]

end SmallCusp
