import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation37B11

namespace SmallCusp

def sourceCoverageTargetSlice37B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice37B10 ++
  sourceCoverageTargetSlice37B11

theorem sourceCoverageTargetSlice37B1_targetConsistent :
    sourceCoverageTargetSlice37B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice37B1,
    sourceCoverageTargetSlice37B10_targetConsistent,
    sourceCoverageTargetSlice37B11_targetConsistent]

theorem sourceCoverageTargetSlice37B1_length : sourceCoverageTargetSlice37B1.length = 125 := by
  simp [sourceCoverageTargetSlice37B1,
    sourceCoverageTargetSlice37B10_length,
    sourceCoverageTargetSlice37B11_length]

end SmallCusp
