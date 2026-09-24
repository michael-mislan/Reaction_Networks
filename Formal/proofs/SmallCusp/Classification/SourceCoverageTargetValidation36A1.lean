import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A11

namespace SmallCusp

def sourceCoverageTargetSlice36A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36A10 ++
  sourceCoverageTargetSlice36A11

theorem sourceCoverageTargetSlice36A1_targetConsistent :
    sourceCoverageTargetSlice36A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36A1,
    sourceCoverageTargetSlice36A10_targetConsistent,
    sourceCoverageTargetSlice36A11_targetConsistent]

theorem sourceCoverageTargetSlice36A1_length : sourceCoverageTargetSlice36A1.length = 125 := by
  simp [sourceCoverageTargetSlice36A1,
    sourceCoverageTargetSlice36A10_length,
    sourceCoverageTargetSlice36A11_length]

end SmallCusp
