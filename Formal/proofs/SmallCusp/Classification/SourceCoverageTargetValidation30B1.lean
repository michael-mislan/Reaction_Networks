import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B11

namespace SmallCusp

def sourceCoverageTargetSlice30B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30B10 ++
  sourceCoverageTargetSlice30B11

theorem sourceCoverageTargetSlice30B1_targetConsistent :
    sourceCoverageTargetSlice30B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30B1,
    sourceCoverageTargetSlice30B10_targetConsistent,
    sourceCoverageTargetSlice30B11_targetConsistent]

theorem sourceCoverageTargetSlice30B1_length : sourceCoverageTargetSlice30B1.length = 125 := by
  simp [sourceCoverageTargetSlice30B1,
    sourceCoverageTargetSlice30B10_length,
    sourceCoverageTargetSlice30B11_length]

end SmallCusp
