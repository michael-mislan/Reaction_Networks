import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B1

namespace SmallCusp

def sourceCoverageTargetSlice24B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24B0 ++
  sourceCoverageTargetSlice24B1

theorem sourceCoverageTargetSlice24B_targetConsistent :
    sourceCoverageTargetSlice24B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24B,
    sourceCoverageTargetSlice24B0_targetConsistent,
    sourceCoverageTargetSlice24B1_targetConsistent]

theorem sourceCoverageTargetSlice24B_length : sourceCoverageTargetSlice24B.length = 250 := by
  simp [sourceCoverageTargetSlice24B,
    sourceCoverageTargetSlice24B0_length,
    sourceCoverageTargetSlice24B1_length]

end SmallCusp
