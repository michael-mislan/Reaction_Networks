import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A11

namespace SmallCusp

def sourceCoverageTargetSlice32A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32A10 ++
  sourceCoverageTargetSlice32A11

theorem sourceCoverageTargetSlice32A1_targetConsistent :
    sourceCoverageTargetSlice32A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32A1,
    sourceCoverageTargetSlice32A10_targetConsistent,
    sourceCoverageTargetSlice32A11_targetConsistent]

theorem sourceCoverageTargetSlice32A1_length : sourceCoverageTargetSlice32A1.length = 125 := by
  simp [sourceCoverageTargetSlice32A1,
    sourceCoverageTargetSlice32A10_length,
    sourceCoverageTargetSlice32A11_length]

end SmallCusp
