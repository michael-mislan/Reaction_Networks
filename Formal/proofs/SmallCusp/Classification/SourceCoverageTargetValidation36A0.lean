import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation36A01

namespace SmallCusp

def sourceCoverageTargetSlice36A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice36A00 ++
  sourceCoverageTargetSlice36A01

theorem sourceCoverageTargetSlice36A0_targetConsistent :
    sourceCoverageTargetSlice36A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice36A0,
    sourceCoverageTargetSlice36A00_targetConsistent,
    sourceCoverageTargetSlice36A01_targetConsistent]

theorem sourceCoverageTargetSlice36A0_length : sourceCoverageTargetSlice36A0.length = 125 := by
  simp [sourceCoverageTargetSlice36A0,
    sourceCoverageTargetSlice36A00_length,
    sourceCoverageTargetSlice36A01_length]

end SmallCusp
