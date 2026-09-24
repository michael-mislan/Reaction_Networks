import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A1

namespace SmallCusp

def sourceCoverageTargetSlice33A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33A0 ++
  sourceCoverageTargetSlice33A1

theorem sourceCoverageTargetSlice33A_targetConsistent :
    sourceCoverageTargetSlice33A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33A,
    sourceCoverageTargetSlice33A0_targetConsistent,
    sourceCoverageTargetSlice33A1_targetConsistent]

theorem sourceCoverageTargetSlice33A_length : sourceCoverageTargetSlice33A.length = 250 := by
  simp [sourceCoverageTargetSlice33A,
    sourceCoverageTargetSlice33A0_length,
    sourceCoverageTargetSlice33A1_length]

end SmallCusp
