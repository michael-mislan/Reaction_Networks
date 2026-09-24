import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A11

namespace SmallCusp

def sourceCoverageTargetSlice45A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45A10 ++
  sourceCoverageTargetSlice45A11

theorem sourceCoverageTargetSlice45A1_targetConsistent :
    sourceCoverageTargetSlice45A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45A1,
    sourceCoverageTargetSlice45A10_targetConsistent,
    sourceCoverageTargetSlice45A11_targetConsistent]

theorem sourceCoverageTargetSlice45A1_length : sourceCoverageTargetSlice45A1.length = 125 := by
  simp [sourceCoverageTargetSlice45A1,
    sourceCoverageTargetSlice45A10_length,
    sourceCoverageTargetSlice45A11_length]

end SmallCusp
