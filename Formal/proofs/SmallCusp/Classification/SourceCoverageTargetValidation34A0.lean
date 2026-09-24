import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation34A01

namespace SmallCusp

def sourceCoverageTargetSlice34A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice34A00 ++
  sourceCoverageTargetSlice34A01

theorem sourceCoverageTargetSlice34A0_targetConsistent :
    sourceCoverageTargetSlice34A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice34A0,
    sourceCoverageTargetSlice34A00_targetConsistent,
    sourceCoverageTargetSlice34A01_targetConsistent]

theorem sourceCoverageTargetSlice34A0_length : sourceCoverageTargetSlice34A0.length = 125 := by
  simp [sourceCoverageTargetSlice34A0,
    sourceCoverageTargetSlice34A00_length,
    sourceCoverageTargetSlice34A01_length]

end SmallCusp
