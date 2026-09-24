import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation55A1

namespace SmallCusp

def sourceCoverageTargetSlice55A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice55A0 ++
  sourceCoverageTargetSlice55A1

theorem sourceCoverageTargetSlice55A_targetConsistent :
    sourceCoverageTargetSlice55A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice55A,
    sourceCoverageTargetSlice55A0_targetConsistent,
    sourceCoverageTargetSlice55A1_targetConsistent]

theorem sourceCoverageTargetSlice55A_length : sourceCoverageTargetSlice55A.length = 250 := by
  simp [sourceCoverageTargetSlice55A,
    sourceCoverageTargetSlice55A0_length,
    sourceCoverageTargetSlice55A1_length]

end SmallCusp
