import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B1

namespace SmallCusp

def sourceCoverageTargetSlice34B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34B0 ++
  sourceCoverageTargetSlice34B1

theorem sourceCoverageTargetSlice34B_targetConsistent :
    sourceCoverageTargetSlice34B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34B,
    sourceCoverageTargetSlice34B0_targetConsistent,
    sourceCoverageTargetSlice34B1_targetConsistent]

theorem sourceCoverageTargetSlice34B_length : sourceCoverageTargetSlice34B.length = 250 := by
  simp [sourceCoverageTargetSlice34B,
    sourceCoverageTargetSlice34B0_length,
    sourceCoverageTargetSlice34B1_length]

end SmallCusp
