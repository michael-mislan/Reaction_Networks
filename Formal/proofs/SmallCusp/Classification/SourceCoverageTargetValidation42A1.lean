import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A11

namespace SmallCusp

def sourceCoverageTargetSlice42A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42A10 ++
  sourceCoverageTargetSlice42A11

theorem sourceCoverageTargetSlice42A1_targetConsistent :
    sourceCoverageTargetSlice42A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42A1,
    sourceCoverageTargetSlice42A10_targetConsistent,
    sourceCoverageTargetSlice42A11_targetConsistent]

theorem sourceCoverageTargetSlice42A1_length : sourceCoverageTargetSlice42A1.length = 125 := by
  simp [sourceCoverageTargetSlice42A1,
    sourceCoverageTargetSlice42A10_length,
    sourceCoverageTargetSlice42A11_length]

end SmallCusp
