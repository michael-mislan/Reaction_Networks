import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation18A1

namespace SmallCusp

def sourceCoverageTargetSlice18A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice18A0 ++
  sourceCoverageTargetSlice18A1

theorem sourceCoverageTargetSlice18A_targetConsistent :
    sourceCoverageTargetSlice18A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice18A,
    sourceCoverageTargetSlice18A0_targetConsistent,
    sourceCoverageTargetSlice18A1_targetConsistent]

theorem sourceCoverageTargetSlice18A_length : sourceCoverageTargetSlice18A.length = 250 := by
  simp [sourceCoverageTargetSlice18A,
    sourceCoverageTargetSlice18A0_length,
    sourceCoverageTargetSlice18A1_length]

end SmallCusp
