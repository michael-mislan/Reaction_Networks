import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A1

namespace SmallCusp

def sourceCoverageTargetSlice42A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42A0 ++
  sourceCoverageTargetSlice42A1

theorem sourceCoverageTargetSlice42A_targetConsistent :
    sourceCoverageTargetSlice42A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42A,
    sourceCoverageTargetSlice42A0_targetConsistent,
    sourceCoverageTargetSlice42A1_targetConsistent]

theorem sourceCoverageTargetSlice42A_length : sourceCoverageTargetSlice42A.length = 250 := by
  simp [sourceCoverageTargetSlice42A,
    sourceCoverageTargetSlice42A0_length,
    sourceCoverageTargetSlice42A1_length]

end SmallCusp
