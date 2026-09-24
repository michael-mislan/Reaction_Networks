import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation15A01

namespace SmallCusp

def sourceCoverageTargetSlice15A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice15A00 ++
  sourceCoverageTargetSlice15A01

theorem sourceCoverageTargetSlice15A0_targetConsistent :
    sourceCoverageTargetSlice15A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice15A0,
    sourceCoverageTargetSlice15A00_targetConsistent,
    sourceCoverageTargetSlice15A01_targetConsistent]

theorem sourceCoverageTargetSlice15A0_length : sourceCoverageTargetSlice15A0.length = 125 := by
  simp [sourceCoverageTargetSlice15A0,
    sourceCoverageTargetSlice15A00_length,
    sourceCoverageTargetSlice15A01_length]

end SmallCusp
