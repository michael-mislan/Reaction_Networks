import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23B01

namespace SmallCusp

def sourceCoverageTargetSlice23B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23B00 ++
  sourceCoverageTargetSlice23B01

theorem sourceCoverageTargetSlice23B0_targetConsistent :
    sourceCoverageTargetSlice23B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23B0,
    sourceCoverageTargetSlice23B00_targetConsistent,
    sourceCoverageTargetSlice23B01_targetConsistent]

theorem sourceCoverageTargetSlice23B0_length : sourceCoverageTargetSlice23B0.length = 125 := by
  simp [sourceCoverageTargetSlice23B0,
    sourceCoverageTargetSlice23B00_length,
    sourceCoverageTargetSlice23B01_length]

end SmallCusp
