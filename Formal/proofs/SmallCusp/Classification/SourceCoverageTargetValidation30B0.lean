import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30B01

namespace SmallCusp

def sourceCoverageTargetSlice30B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30B00 ++
  sourceCoverageTargetSlice30B01

theorem sourceCoverageTargetSlice30B0_targetConsistent :
    sourceCoverageTargetSlice30B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30B0,
    sourceCoverageTargetSlice30B00_targetConsistent,
    sourceCoverageTargetSlice30B01_targetConsistent]

theorem sourceCoverageTargetSlice30B0_length : sourceCoverageTargetSlice30B0.length = 125 := by
  simp [sourceCoverageTargetSlice30B0,
    sourceCoverageTargetSlice30B00_length,
    sourceCoverageTargetSlice30B01_length]

end SmallCusp
