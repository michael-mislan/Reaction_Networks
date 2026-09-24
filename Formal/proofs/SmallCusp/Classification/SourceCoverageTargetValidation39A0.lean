import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A01

namespace SmallCusp

def sourceCoverageTargetSlice39A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39A00 ++
  sourceCoverageTargetSlice39A01

theorem sourceCoverageTargetSlice39A0_targetConsistent :
    sourceCoverageTargetSlice39A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39A0,
    sourceCoverageTargetSlice39A00_targetConsistent,
    sourceCoverageTargetSlice39A01_targetConsistent]

theorem sourceCoverageTargetSlice39A0_length : sourceCoverageTargetSlice39A0.length = 125 := by
  simp [sourceCoverageTargetSlice39A0,
    sourceCoverageTargetSlice39A00_length,
    sourceCoverageTargetSlice39A01_length]

end SmallCusp
