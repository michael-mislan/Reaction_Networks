import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A01

namespace SmallCusp

def sourceCoverageTargetSlice40A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40A00 ++
  sourceCoverageTargetSlice40A01

theorem sourceCoverageTargetSlice40A0_targetConsistent :
    sourceCoverageTargetSlice40A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40A0,
    sourceCoverageTargetSlice40A00_targetConsistent,
    sourceCoverageTargetSlice40A01_targetConsistent]

theorem sourceCoverageTargetSlice40A0_length : sourceCoverageTargetSlice40A0.length = 125 := by
  simp [sourceCoverageTargetSlice40A0,
    sourceCoverageTargetSlice40A00_length,
    sourceCoverageTargetSlice40A01_length]

end SmallCusp
