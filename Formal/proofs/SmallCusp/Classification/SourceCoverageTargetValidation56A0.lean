import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation56A01

namespace SmallCusp

def sourceCoverageTargetSlice56A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice56A00 ++
  sourceCoverageTargetSlice56A01

theorem sourceCoverageTargetSlice56A0_targetConsistent :
    sourceCoverageTargetSlice56A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice56A0,
    sourceCoverageTargetSlice56A00_targetConsistent,
    sourceCoverageTargetSlice56A01_targetConsistent]

theorem sourceCoverageTargetSlice56A0_length : sourceCoverageTargetSlice56A0.length = 125 := by
  simp [sourceCoverageTargetSlice56A0,
    sourceCoverageTargetSlice56A00_length,
    sourceCoverageTargetSlice56A01_length]

end SmallCusp
