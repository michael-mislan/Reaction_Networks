import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A11

namespace SmallCusp

def sourceCoverageTargetSlice46A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46A10 ++
  sourceCoverageTargetSlice46A11

theorem sourceCoverageTargetSlice46A1_targetConsistent :
    sourceCoverageTargetSlice46A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46A1,
    sourceCoverageTargetSlice46A10_targetConsistent,
    sourceCoverageTargetSlice46A11_targetConsistent]

theorem sourceCoverageTargetSlice46A1_length : sourceCoverageTargetSlice46A1.length = 125 := by
  simp [sourceCoverageTargetSlice46A1,
    sourceCoverageTargetSlice46A10_length,
    sourceCoverageTargetSlice46A11_length]

end SmallCusp
