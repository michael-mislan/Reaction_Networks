import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation44A01

namespace SmallCusp

def sourceCoverageTargetSlice44A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice44A00 ++
  sourceCoverageTargetSlice44A01

theorem sourceCoverageTargetSlice44A0_targetConsistent :
    sourceCoverageTargetSlice44A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice44A0,
    sourceCoverageTargetSlice44A00_targetConsistent,
    sourceCoverageTargetSlice44A01_targetConsistent]

theorem sourceCoverageTargetSlice44A0_length : sourceCoverageTargetSlice44A0.length = 125 := by
  simp [sourceCoverageTargetSlice44A0,
    sourceCoverageTargetSlice44A00_length,
    sourceCoverageTargetSlice44A01_length]

end SmallCusp
