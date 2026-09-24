import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B11

namespace SmallCusp

def sourceCoverageTargetSlice18B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18B10 ++
  sourceCoverageTargetSlice18B11

theorem sourceCoverageTargetSlice18B1_targetConsistent :
    sourceCoverageTargetSlice18B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18B1,
    sourceCoverageTargetSlice18B10_targetConsistent,
    sourceCoverageTargetSlice18B11_targetConsistent]

theorem sourceCoverageTargetSlice18B1_length : sourceCoverageTargetSlice18B1.length = 125 := by
  simp [sourceCoverageTargetSlice18B1,
    sourceCoverageTargetSlice18B10_length,
    sourceCoverageTargetSlice18B11_length]

end SmallCusp
