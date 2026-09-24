import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation13A1

namespace SmallCusp

def sourceCoverageTargetSlice13A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice13A0 ++
  sourceCoverageTargetSlice13A1

theorem sourceCoverageTargetSlice13A_targetConsistent :
    sourceCoverageTargetSlice13A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice13A,
    sourceCoverageTargetSlice13A0_targetConsistent,
    sourceCoverageTargetSlice13A1_targetConsistent]

theorem sourceCoverageTargetSlice13A_length : sourceCoverageTargetSlice13A.length = 250 := by
  simp [sourceCoverageTargetSlice13A,
    sourceCoverageTargetSlice13A0_length,
    sourceCoverageTargetSlice13A1_length]

end SmallCusp
