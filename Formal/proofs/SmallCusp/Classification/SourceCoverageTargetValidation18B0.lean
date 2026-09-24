import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B01

namespace SmallCusp

def sourceCoverageTargetSlice18B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18B00 ++
  sourceCoverageTargetSlice18B01

theorem sourceCoverageTargetSlice18B0_targetConsistent :
    sourceCoverageTargetSlice18B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18B0,
    sourceCoverageTargetSlice18B00_targetConsistent,
    sourceCoverageTargetSlice18B01_targetConsistent]

theorem sourceCoverageTargetSlice18B0_length : sourceCoverageTargetSlice18B0.length = 125 := by
  simp [sourceCoverageTargetSlice18B0,
    sourceCoverageTargetSlice18B00_length,
    sourceCoverageTargetSlice18B01_length]

end SmallCusp
