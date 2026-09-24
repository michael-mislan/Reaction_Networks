import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A11

namespace SmallCusp

def sourceCoverageTargetSlice24A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24A10 ++
  sourceCoverageTargetSlice24A11

theorem sourceCoverageTargetSlice24A1_targetConsistent :
    sourceCoverageTargetSlice24A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24A1,
    sourceCoverageTargetSlice24A10_targetConsistent,
    sourceCoverageTargetSlice24A11_targetConsistent]

theorem sourceCoverageTargetSlice24A1_length : sourceCoverageTargetSlice24A1.length = 125 := by
  simp [sourceCoverageTargetSlice24A1,
    sourceCoverageTargetSlice24A10_length,
    sourceCoverageTargetSlice24A11_length]

end SmallCusp
