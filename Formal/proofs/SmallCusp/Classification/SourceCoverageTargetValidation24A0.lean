import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A01

namespace SmallCusp

def sourceCoverageTargetSlice24A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24A00 ++
  sourceCoverageTargetSlice24A01

theorem sourceCoverageTargetSlice24A0_targetConsistent :
    sourceCoverageTargetSlice24A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24A0,
    sourceCoverageTargetSlice24A00_targetConsistent,
    sourceCoverageTargetSlice24A01_targetConsistent]

theorem sourceCoverageTargetSlice24A0_length : sourceCoverageTargetSlice24A0.length = 125 := by
  simp [sourceCoverageTargetSlice24A0,
    sourceCoverageTargetSlice24A00_length,
    sourceCoverageTargetSlice24A01_length]

end SmallCusp
