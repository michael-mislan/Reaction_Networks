import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22B1

namespace SmallCusp

def sourceCoverageTargetSlice22B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22B0 ++
  sourceCoverageTargetSlice22B1

theorem sourceCoverageTargetSlice22B_targetConsistent :
    sourceCoverageTargetSlice22B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22B,
    sourceCoverageTargetSlice22B0_targetConsistent,
    sourceCoverageTargetSlice22B1_targetConsistent]

theorem sourceCoverageTargetSlice22B_length : sourceCoverageTargetSlice22B.length = 250 := by
  simp [sourceCoverageTargetSlice22B,
    sourceCoverageTargetSlice22B0_length,
    sourceCoverageTargetSlice22B1_length]

end SmallCusp
