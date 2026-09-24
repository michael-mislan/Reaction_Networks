import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B1

namespace SmallCusp

def sourceCoverageTargetSlice30B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30B0 ++
  sourceCoverageTargetSlice30B1

theorem sourceCoverageTargetSlice30B_targetConsistent :
    sourceCoverageTargetSlice30B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30B,
    sourceCoverageTargetSlice30B0_targetConsistent,
    sourceCoverageTargetSlice30B1_targetConsistent]

theorem sourceCoverageTargetSlice30B_length : sourceCoverageTargetSlice30B.length = 250 := by
  simp [sourceCoverageTargetSlice30B,
    sourceCoverageTargetSlice30B0_length,
    sourceCoverageTargetSlice30B1_length]

end SmallCusp
