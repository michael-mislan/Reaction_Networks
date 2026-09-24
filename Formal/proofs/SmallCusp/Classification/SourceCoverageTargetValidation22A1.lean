import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A11

namespace SmallCusp

def sourceCoverageTargetSlice22A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22A10 ++
  sourceCoverageTargetSlice22A11

theorem sourceCoverageTargetSlice22A1_targetConsistent :
    sourceCoverageTargetSlice22A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22A1,
    sourceCoverageTargetSlice22A10_targetConsistent,
    sourceCoverageTargetSlice22A11_targetConsistent]

theorem sourceCoverageTargetSlice22A1_length : sourceCoverageTargetSlice22A1.length = 125 := by
  simp [sourceCoverageTargetSlice22A1,
    sourceCoverageTargetSlice22A10_length,
    sourceCoverageTargetSlice22A11_length]

end SmallCusp
