import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation30A11

namespace SmallCusp

def sourceCoverageTargetSlice30A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice30A10 ++
  sourceCoverageTargetSlice30A11

theorem sourceCoverageTargetSlice30A1_targetConsistent :
    sourceCoverageTargetSlice30A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice30A1,
    sourceCoverageTargetSlice30A10_targetConsistent,
    sourceCoverageTargetSlice30A11_targetConsistent]

theorem sourceCoverageTargetSlice30A1_length : sourceCoverageTargetSlice30A1.length = 125 := by
  simp [sourceCoverageTargetSlice30A1,
    sourceCoverageTargetSlice30A10_length,
    sourceCoverageTargetSlice30A11_length]

end SmallCusp
