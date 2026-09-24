import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A1

namespace SmallCusp

def sourceCoverageTargetSlice19A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19A0 ++
  sourceCoverageTargetSlice19A1

theorem sourceCoverageTargetSlice19A_targetConsistent :
    sourceCoverageTargetSlice19A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19A,
    sourceCoverageTargetSlice19A0_targetConsistent,
    sourceCoverageTargetSlice19A1_targetConsistent]

theorem sourceCoverageTargetSlice19A_length : sourceCoverageTargetSlice19A.length = 250 := by
  simp [sourceCoverageTargetSlice19A,
    sourceCoverageTargetSlice19A0_length,
    sourceCoverageTargetSlice19A1_length]

end SmallCusp
