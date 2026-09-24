import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18B1

namespace SmallCusp

def sourceCoverageTargetSlice18B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18B0 ++
  sourceCoverageTargetSlice18B1

theorem sourceCoverageTargetSlice18B_targetConsistent :
    sourceCoverageTargetSlice18B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18B,
    sourceCoverageTargetSlice18B0_targetConsistent,
    sourceCoverageTargetSlice18B1_targetConsistent]

theorem sourceCoverageTargetSlice18B_length : sourceCoverageTargetSlice18B.length = 250 := by
  simp [sourceCoverageTargetSlice18B,
    sourceCoverageTargetSlice18B0_length,
    sourceCoverageTargetSlice18B1_length]

end SmallCusp
