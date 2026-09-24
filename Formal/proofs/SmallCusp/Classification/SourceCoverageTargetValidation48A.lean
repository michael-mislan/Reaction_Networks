import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A1

namespace SmallCusp

def sourceCoverageTargetSlice48A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48A0 ++
  sourceCoverageTargetSlice48A1

theorem sourceCoverageTargetSlice48A_targetConsistent :
    sourceCoverageTargetSlice48A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48A,
    sourceCoverageTargetSlice48A0_targetConsistent,
    sourceCoverageTargetSlice48A1_targetConsistent]

theorem sourceCoverageTargetSlice48A_length : sourceCoverageTargetSlice48A.length = 250 := by
  simp [sourceCoverageTargetSlice48A,
    sourceCoverageTargetSlice48A0_length,
    sourceCoverageTargetSlice48A1_length]

end SmallCusp
