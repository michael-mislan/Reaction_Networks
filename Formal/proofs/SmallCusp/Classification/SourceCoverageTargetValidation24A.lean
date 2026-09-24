import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24A1

namespace SmallCusp

def sourceCoverageTargetSlice24A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24A0 ++
  sourceCoverageTargetSlice24A1

theorem sourceCoverageTargetSlice24A_targetConsistent :
    sourceCoverageTargetSlice24A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24A,
    sourceCoverageTargetSlice24A0_targetConsistent,
    sourceCoverageTargetSlice24A1_targetConsistent]

theorem sourceCoverageTargetSlice24A_length : sourceCoverageTargetSlice24A.length = 250 := by
  simp [sourceCoverageTargetSlice24A,
    sourceCoverageTargetSlice24A0_length,
    sourceCoverageTargetSlice24A1_length]

end SmallCusp
