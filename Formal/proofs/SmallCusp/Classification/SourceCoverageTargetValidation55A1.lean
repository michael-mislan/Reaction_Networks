import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A11

namespace SmallCusp

def sourceCoverageTargetSlice55A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55A10 ++
  sourceCoverageTargetSlice55A11

theorem sourceCoverageTargetSlice55A1_targetConsistent :
    sourceCoverageTargetSlice55A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55A1,
    sourceCoverageTargetSlice55A10_targetConsistent,
    sourceCoverageTargetSlice55A11_targetConsistent]

theorem sourceCoverageTargetSlice55A1_length : sourceCoverageTargetSlice55A1.length = 125 := by
  simp [sourceCoverageTargetSlice55A1,
    sourceCoverageTargetSlice55A10_length,
    sourceCoverageTargetSlice55A11_length]

end SmallCusp
