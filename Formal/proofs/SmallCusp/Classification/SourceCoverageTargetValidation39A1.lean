import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A11

namespace SmallCusp

def sourceCoverageTargetSlice39A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39A10 ++
  sourceCoverageTargetSlice39A11

theorem sourceCoverageTargetSlice39A1_targetConsistent :
    sourceCoverageTargetSlice39A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39A1,
    sourceCoverageTargetSlice39A10_targetConsistent,
    sourceCoverageTargetSlice39A11_targetConsistent]

theorem sourceCoverageTargetSlice39A1_length : sourceCoverageTargetSlice39A1.length = 125 := by
  simp [sourceCoverageTargetSlice39A1,
    sourceCoverageTargetSlice39A10_length,
    sourceCoverageTargetSlice39A11_length]

end SmallCusp
