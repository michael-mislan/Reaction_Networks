import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation58A01

namespace SmallCusp

def sourceCoverageTargetSlice58A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice58A00 ++
  sourceCoverageTargetSlice58A01

theorem sourceCoverageTargetSlice58A0_targetConsistent :
    sourceCoverageTargetSlice58A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice58A0,
    sourceCoverageTargetSlice58A00_targetConsistent,
    sourceCoverageTargetSlice58A01_targetConsistent]

theorem sourceCoverageTargetSlice58A0_length : sourceCoverageTargetSlice58A0.length = 125 := by
  simp [sourceCoverageTargetSlice58A0,
    sourceCoverageTargetSlice58A00_length,
    sourceCoverageTargetSlice58A01_length]

end SmallCusp
