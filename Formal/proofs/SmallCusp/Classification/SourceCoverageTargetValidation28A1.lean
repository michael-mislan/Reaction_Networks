import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation28A11

namespace SmallCusp

def sourceCoverageTargetSlice28A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice28A10 ++
  sourceCoverageTargetSlice28A11

theorem sourceCoverageTargetSlice28A1_targetConsistent :
    sourceCoverageTargetSlice28A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice28A1,
    sourceCoverageTargetSlice28A10_targetConsistent,
    sourceCoverageTargetSlice28A11_targetConsistent]

theorem sourceCoverageTargetSlice28A1_length : sourceCoverageTargetSlice28A1.length = 125 := by
  simp [sourceCoverageTargetSlice28A1,
    sourceCoverageTargetSlice28A10_length,
    sourceCoverageTargetSlice28A11_length]

end SmallCusp
