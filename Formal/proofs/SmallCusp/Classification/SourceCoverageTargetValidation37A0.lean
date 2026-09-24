import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37A01

namespace SmallCusp

def sourceCoverageTargetSlice37A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37A00 ++
  sourceCoverageTargetSlice37A01

theorem sourceCoverageTargetSlice37A0_targetConsistent :
    sourceCoverageTargetSlice37A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37A0,
    sourceCoverageTargetSlice37A00_targetConsistent,
    sourceCoverageTargetSlice37A01_targetConsistent]

theorem sourceCoverageTargetSlice37A0_length : sourceCoverageTargetSlice37A0.length = 125 := by
  simp [sourceCoverageTargetSlice37A0,
    sourceCoverageTargetSlice37A00_length,
    sourceCoverageTargetSlice37A01_length]

end SmallCusp
