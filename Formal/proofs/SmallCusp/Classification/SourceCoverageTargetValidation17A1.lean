import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A11

namespace SmallCusp

def sourceCoverageTargetSlice17A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17A10 ++
  sourceCoverageTargetSlice17A11

theorem sourceCoverageTargetSlice17A1_targetConsistent :
    sourceCoverageTargetSlice17A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17A1,
    sourceCoverageTargetSlice17A10_targetConsistent,
    sourceCoverageTargetSlice17A11_targetConsistent]

theorem sourceCoverageTargetSlice17A1_length : sourceCoverageTargetSlice17A1.length = 125 := by
  simp [sourceCoverageTargetSlice17A1,
    sourceCoverageTargetSlice17A10_length,
    sourceCoverageTargetSlice17A11_length]

end SmallCusp
