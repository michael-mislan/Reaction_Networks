import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A1

namespace SmallCusp

def sourceCoverageTargetSlice36A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36A0 ++
  sourceCoverageTargetSlice36A1

theorem sourceCoverageTargetSlice36A_targetConsistent :
    sourceCoverageTargetSlice36A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36A,
    sourceCoverageTargetSlice36A0_targetConsistent,
    sourceCoverageTargetSlice36A1_targetConsistent]

theorem sourceCoverageTargetSlice36A_length : sourceCoverageTargetSlice36A.length = 250 := by
  simp [sourceCoverageTargetSlice36A,
    sourceCoverageTargetSlice36A0_length,
    sourceCoverageTargetSlice36A1_length]

end SmallCusp
