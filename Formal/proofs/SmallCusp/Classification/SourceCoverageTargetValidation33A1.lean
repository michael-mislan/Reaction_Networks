import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation33A11

namespace SmallCusp

def sourceCoverageTargetSlice33A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice33A10 ++
  sourceCoverageTargetSlice33A11

theorem sourceCoverageTargetSlice33A1_targetConsistent :
    sourceCoverageTargetSlice33A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice33A1,
    sourceCoverageTargetSlice33A10_targetConsistent,
    sourceCoverageTargetSlice33A11_targetConsistent]

theorem sourceCoverageTargetSlice33A1_length : sourceCoverageTargetSlice33A1.length = 125 := by
  simp [sourceCoverageTargetSlice33A1,
    sourceCoverageTargetSlice33A10_length,
    sourceCoverageTargetSlice33A11_length]

end SmallCusp
