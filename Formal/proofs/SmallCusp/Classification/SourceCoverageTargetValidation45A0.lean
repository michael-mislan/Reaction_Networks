import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45A01

namespace SmallCusp

def sourceCoverageTargetSlice45A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45A00 ++
  sourceCoverageTargetSlice45A01

theorem sourceCoverageTargetSlice45A0_targetConsistent :
    sourceCoverageTargetSlice45A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45A0,
    sourceCoverageTargetSlice45A00_targetConsistent,
    sourceCoverageTargetSlice45A01_targetConsistent]

theorem sourceCoverageTargetSlice45A0_length : sourceCoverageTargetSlice45A0.length = 125 := by
  simp [sourceCoverageTargetSlice45A0,
    sourceCoverageTargetSlice45A00_length,
    sourceCoverageTargetSlice45A01_length]

end SmallCusp
