import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A01

namespace SmallCusp

def sourceCoverageTargetSlice18A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18A00 ++
  sourceCoverageTargetSlice18A01

theorem sourceCoverageTargetSlice18A0_targetConsistent :
    sourceCoverageTargetSlice18A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18A0,
    sourceCoverageTargetSlice18A00_targetConsistent,
    sourceCoverageTargetSlice18A01_targetConsistent]

theorem sourceCoverageTargetSlice18A0_length : sourceCoverageTargetSlice18A0.length = 125 := by
  simp [sourceCoverageTargetSlice18A0,
    sourceCoverageTargetSlice18A00_length,
    sourceCoverageTargetSlice18A01_length]

end SmallCusp
