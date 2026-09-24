import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B11

namespace SmallCusp

def sourceCoverageTargetSlice23B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23B10 ++
  sourceCoverageTargetSlice23B11

theorem sourceCoverageTargetSlice23B1_targetConsistent :
    sourceCoverageTargetSlice23B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23B1,
    sourceCoverageTargetSlice23B10_targetConsistent,
    sourceCoverageTargetSlice23B11_targetConsistent]

theorem sourceCoverageTargetSlice23B1_length : sourceCoverageTargetSlice23B1.length = 125 := by
  simp [sourceCoverageTargetSlice23B1,
    sourceCoverageTargetSlice23B10_length,
    sourceCoverageTargetSlice23B11_length]

end SmallCusp
