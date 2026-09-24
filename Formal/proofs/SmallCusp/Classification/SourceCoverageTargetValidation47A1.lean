import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A11

namespace SmallCusp

def sourceCoverageTargetSlice47A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47A10 ++
  sourceCoverageTargetSlice47A11

theorem sourceCoverageTargetSlice47A1_targetConsistent :
    sourceCoverageTargetSlice47A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47A1,
    sourceCoverageTargetSlice47A10_targetConsistent,
    sourceCoverageTargetSlice47A11_targetConsistent]

theorem sourceCoverageTargetSlice47A1_length : sourceCoverageTargetSlice47A1.length = 125 := by
  simp [sourceCoverageTargetSlice47A1,
    sourceCoverageTargetSlice47A10_length,
    sourceCoverageTargetSlice47A11_length]

end SmallCusp
