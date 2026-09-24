import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B1

namespace SmallCusp

def sourceCoverageTargetSlice23B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23B0 ++
  sourceCoverageTargetSlice23B1

theorem sourceCoverageTargetSlice23B_targetConsistent :
    sourceCoverageTargetSlice23B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23B,
    sourceCoverageTargetSlice23B0_targetConsistent,
    sourceCoverageTargetSlice23B1_targetConsistent]

theorem sourceCoverageTargetSlice23B_length : sourceCoverageTargetSlice23B.length = 250 := by
  simp [sourceCoverageTargetSlice23B,
    sourceCoverageTargetSlice23B0_length,
    sourceCoverageTargetSlice23B1_length]

end SmallCusp
