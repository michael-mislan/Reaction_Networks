import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A1

namespace SmallCusp

def sourceCoverageTargetSlice46A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46A0 ++
  sourceCoverageTargetSlice46A1

theorem sourceCoverageTargetSlice46A_targetConsistent :
    sourceCoverageTargetSlice46A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46A,
    sourceCoverageTargetSlice46A0_targetConsistent,
    sourceCoverageTargetSlice46A1_targetConsistent]

theorem sourceCoverageTargetSlice46A_length : sourceCoverageTargetSlice46A.length = 250 := by
  simp [sourceCoverageTargetSlice46A,
    sourceCoverageTargetSlice46A0_length,
    sourceCoverageTargetSlice46A1_length]

end SmallCusp
