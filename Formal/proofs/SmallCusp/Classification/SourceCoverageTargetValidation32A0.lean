import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation32A01

namespace SmallCusp

def sourceCoverageTargetSlice32A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice32A00 ++
  sourceCoverageTargetSlice32A01

theorem sourceCoverageTargetSlice32A0_targetConsistent :
    sourceCoverageTargetSlice32A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice32A0,
    sourceCoverageTargetSlice32A00_targetConsistent,
    sourceCoverageTargetSlice32A01_targetConsistent]

theorem sourceCoverageTargetSlice32A0_length : sourceCoverageTargetSlice32A0.length = 125 := by
  simp [sourceCoverageTargetSlice32A0,
    sourceCoverageTargetSlice32A00_length,
    sourceCoverageTargetSlice32A01_length]

end SmallCusp
