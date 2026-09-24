import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A1

namespace SmallCusp

def sourceCoverageTargetSlice47A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47A0 ++
  sourceCoverageTargetSlice47A1

theorem sourceCoverageTargetSlice47A_targetConsistent :
    sourceCoverageTargetSlice47A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47A,
    sourceCoverageTargetSlice47A0_targetConsistent,
    sourceCoverageTargetSlice47A1_targetConsistent]

theorem sourceCoverageTargetSlice47A_length : sourceCoverageTargetSlice47A.length = 250 := by
  simp [sourceCoverageTargetSlice47A,
    sourceCoverageTargetSlice47A0_length,
    sourceCoverageTargetSlice47A1_length]

end SmallCusp
