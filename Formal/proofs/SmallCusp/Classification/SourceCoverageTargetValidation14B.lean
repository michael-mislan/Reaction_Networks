import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation14B1

namespace SmallCusp

def sourceCoverageTargetSlice14B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice14B0 ++
  sourceCoverageTargetSlice14B1

theorem sourceCoverageTargetSlice14B_targetConsistent :
    sourceCoverageTargetSlice14B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice14B,
    sourceCoverageTargetSlice14B0_targetConsistent,
    sourceCoverageTargetSlice14B1_targetConsistent]

theorem sourceCoverageTargetSlice14B_length : sourceCoverageTargetSlice14B.length = 250 := by
  simp [sourceCoverageTargetSlice14B,
    sourceCoverageTargetSlice14B0_length,
    sourceCoverageTargetSlice14B1_length]

end SmallCusp
