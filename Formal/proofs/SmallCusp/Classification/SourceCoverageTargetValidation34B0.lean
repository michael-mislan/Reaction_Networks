import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B01

namespace SmallCusp

def sourceCoverageTargetSlice34B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34B00 ++
  sourceCoverageTargetSlice34B01

theorem sourceCoverageTargetSlice34B0_targetConsistent :
    sourceCoverageTargetSlice34B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34B0,
    sourceCoverageTargetSlice34B00_targetConsistent,
    sourceCoverageTargetSlice34B01_targetConsistent]

theorem sourceCoverageTargetSlice34B0_length : sourceCoverageTargetSlice34B0.length = 125 := by
  simp [sourceCoverageTargetSlice34B0,
    sourceCoverageTargetSlice34B00_length,
    sourceCoverageTargetSlice34B01_length]

end SmallCusp
