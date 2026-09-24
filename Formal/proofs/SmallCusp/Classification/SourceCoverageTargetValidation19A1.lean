import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A11

namespace SmallCusp

def sourceCoverageTargetSlice19A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19A10 ++
  sourceCoverageTargetSlice19A11

theorem sourceCoverageTargetSlice19A1_targetConsistent :
    sourceCoverageTargetSlice19A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19A1,
    sourceCoverageTargetSlice19A10_targetConsistent,
    sourceCoverageTargetSlice19A11_targetConsistent]

theorem sourceCoverageTargetSlice19A1_length : sourceCoverageTargetSlice19A1.length = 125 := by
  simp [sourceCoverageTargetSlice19A1,
    sourceCoverageTargetSlice19A10_length,
    sourceCoverageTargetSlice19A11_length]

end SmallCusp
