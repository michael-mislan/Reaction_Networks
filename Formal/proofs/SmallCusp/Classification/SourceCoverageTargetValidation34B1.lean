import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34B11

namespace SmallCusp

def sourceCoverageTargetSlice34B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34B10 ++
  sourceCoverageTargetSlice34B11

theorem sourceCoverageTargetSlice34B1_targetConsistent :
    sourceCoverageTargetSlice34B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34B1,
    sourceCoverageTargetSlice34B10_targetConsistent,
    sourceCoverageTargetSlice34B11_targetConsistent]

theorem sourceCoverageTargetSlice34B1_length : sourceCoverageTargetSlice34B1.length = 125 := by
  simp [sourceCoverageTargetSlice34B1,
    sourceCoverageTargetSlice34B10_length,
    sourceCoverageTargetSlice34B11_length]

end SmallCusp
