import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A11

namespace SmallCusp

def sourceCoverageTargetSlice48A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48A10 ++
  sourceCoverageTargetSlice48A11

theorem sourceCoverageTargetSlice48A1_targetConsistent :
    sourceCoverageTargetSlice48A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48A1,
    sourceCoverageTargetSlice48A10_targetConsistent,
    sourceCoverageTargetSlice48A11_targetConsistent]

theorem sourceCoverageTargetSlice48A1_length : sourceCoverageTargetSlice48A1.length = 125 := by
  simp [sourceCoverageTargetSlice48A1,
    sourceCoverageTargetSlice48A10_length,
    sourceCoverageTargetSlice48A11_length]

end SmallCusp
