import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation39A1

namespace SmallCusp

def sourceCoverageTargetSlice39A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice39A0 ++
  sourceCoverageTargetSlice39A1

theorem sourceCoverageTargetSlice39A_targetConsistent :
    sourceCoverageTargetSlice39A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice39A,
    sourceCoverageTargetSlice39A0_targetConsistent,
    sourceCoverageTargetSlice39A1_targetConsistent]

theorem sourceCoverageTargetSlice39A_length : sourceCoverageTargetSlice39A.length = 250 := by
  simp [sourceCoverageTargetSlice39A,
    sourceCoverageTargetSlice39A0_length,
    sourceCoverageTargetSlice39A1_length]

end SmallCusp
