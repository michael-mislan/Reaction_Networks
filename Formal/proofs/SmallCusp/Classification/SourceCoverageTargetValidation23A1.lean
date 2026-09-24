import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A11

namespace SmallCusp

def sourceCoverageTargetSlice23A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23A10 ++
  sourceCoverageTargetSlice23A11

theorem sourceCoverageTargetSlice23A1_targetConsistent :
    sourceCoverageTargetSlice23A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23A1,
    sourceCoverageTargetSlice23A10_targetConsistent,
    sourceCoverageTargetSlice23A11_targetConsistent]

theorem sourceCoverageTargetSlice23A1_length : sourceCoverageTargetSlice23A1.length = 125 := by
  simp [sourceCoverageTargetSlice23A1,
    sourceCoverageTargetSlice23A10_length,
    sourceCoverageTargetSlice23A11_length]

end SmallCusp
