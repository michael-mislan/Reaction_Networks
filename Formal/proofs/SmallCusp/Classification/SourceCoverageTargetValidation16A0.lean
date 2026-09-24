import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation16A01

namespace SmallCusp

def sourceCoverageTargetSlice16A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice16A00 ++
  sourceCoverageTargetSlice16A01

theorem sourceCoverageTargetSlice16A0_targetConsistent :
    sourceCoverageTargetSlice16A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice16A0,
    sourceCoverageTargetSlice16A00_targetConsistent,
    sourceCoverageTargetSlice16A01_targetConsistent]

theorem sourceCoverageTargetSlice16A0_length : sourceCoverageTargetSlice16A0.length = 125 := by
  simp [sourceCoverageTargetSlice16A0,
    sourceCoverageTargetSlice16A00_length,
    sourceCoverageTargetSlice16A01_length]

end SmallCusp
