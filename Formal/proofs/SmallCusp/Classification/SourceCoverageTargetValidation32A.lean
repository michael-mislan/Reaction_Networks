import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A1

namespace SmallCusp

def sourceCoverageTargetSlice32A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32A0 ++
  sourceCoverageTargetSlice32A1

theorem sourceCoverageTargetSlice32A_targetConsistent :
    sourceCoverageTargetSlice32A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32A,
    sourceCoverageTargetSlice32A0_targetConsistent,
    sourceCoverageTargetSlice32A1_targetConsistent]

theorem sourceCoverageTargetSlice32A_length : sourceCoverageTargetSlice32A.length = 250 := by
  simp [sourceCoverageTargetSlice32A,
    sourceCoverageTargetSlice32A0_length,
    sourceCoverageTargetSlice32A1_length]

end SmallCusp
