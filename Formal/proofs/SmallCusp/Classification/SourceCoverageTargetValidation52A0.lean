import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation52A01

namespace SmallCusp

def sourceCoverageTargetSlice52A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice52A00 ++
  sourceCoverageTargetSlice52A01

theorem sourceCoverageTargetSlice52A0_targetConsistent :
    sourceCoverageTargetSlice52A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice52A0,
    sourceCoverageTargetSlice52A00_targetConsistent,
    sourceCoverageTargetSlice52A01_targetConsistent]

theorem sourceCoverageTargetSlice52A0_length : sourceCoverageTargetSlice52A0.length = 125 := by
  simp [sourceCoverageTargetSlice52A0,
    sourceCoverageTargetSlice52A00_length,
    sourceCoverageTargetSlice52A01_length]

end SmallCusp
