import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation42A01

namespace SmallCusp

def sourceCoverageTargetSlice42A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice42A00 ++
  sourceCoverageTargetSlice42A01

theorem sourceCoverageTargetSlice42A0_targetConsistent :
    sourceCoverageTargetSlice42A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice42A0,
    sourceCoverageTargetSlice42A00_targetConsistent,
    sourceCoverageTargetSlice42A01_targetConsistent]

theorem sourceCoverageTargetSlice42A0_length : sourceCoverageTargetSlice42A0.length = 125 := by
  simp [sourceCoverageTargetSlice42A0,
    sourceCoverageTargetSlice42A00_length,
    sourceCoverageTargetSlice42A01_length]

end SmallCusp
