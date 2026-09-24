import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A1

namespace SmallCusp

def sourceCoverageTargetSlice22A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22A0 ++
  sourceCoverageTargetSlice22A1

theorem sourceCoverageTargetSlice22A_targetConsistent :
    sourceCoverageTargetSlice22A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22A,
    sourceCoverageTargetSlice22A0_targetConsistent,
    sourceCoverageTargetSlice22A1_targetConsistent]

theorem sourceCoverageTargetSlice22A_length : sourceCoverageTargetSlice22A.length = 250 := by
  simp [sourceCoverageTargetSlice22A,
    sourceCoverageTargetSlice22A0_length,
    sourceCoverageTargetSlice22A1_length]

end SmallCusp
