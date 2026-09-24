import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A01

namespace SmallCusp

def sourceCoverageTargetSlice28A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28A00 ++
  sourceCoverageTargetSlice28A01

theorem sourceCoverageTargetSlice28A0_targetConsistent :
    sourceCoverageTargetSlice28A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28A0,
    sourceCoverageTargetSlice28A00_targetConsistent,
    sourceCoverageTargetSlice28A01_targetConsistent]

theorem sourceCoverageTargetSlice28A0_length : sourceCoverageTargetSlice28A0.length = 125 := by
  simp [sourceCoverageTargetSlice28A0,
    sourceCoverageTargetSlice28A00_length,
    sourceCoverageTargetSlice28A01_length]

end SmallCusp
