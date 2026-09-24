import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A11

namespace SmallCusp

def sourceCoverageTargetSlice18A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18A10 ++
  sourceCoverageTargetSlice18A11

theorem sourceCoverageTargetSlice18A1_targetConsistent :
    sourceCoverageTargetSlice18A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18A1,
    sourceCoverageTargetSlice18A10_targetConsistent,
    sourceCoverageTargetSlice18A11_targetConsistent]

theorem sourceCoverageTargetSlice18A1_length : sourceCoverageTargetSlice18A1.length = 125 := by
  simp [sourceCoverageTargetSlice18A1,
    sourceCoverageTargetSlice18A10_length,
    sourceCoverageTargetSlice18A11_length]

end SmallCusp
