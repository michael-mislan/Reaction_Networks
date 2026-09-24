import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation23A01

namespace SmallCusp

def sourceCoverageTargetSlice23A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice23A00 ++
  sourceCoverageTargetSlice23A01

theorem sourceCoverageTargetSlice23A0_targetConsistent :
    sourceCoverageTargetSlice23A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice23A0,
    sourceCoverageTargetSlice23A00_targetConsistent,
    sourceCoverageTargetSlice23A01_targetConsistent]

theorem sourceCoverageTargetSlice23A0_length : sourceCoverageTargetSlice23A0.length = 125 := by
  simp [sourceCoverageTargetSlice23A0,
    sourceCoverageTargetSlice23A00_length,
    sourceCoverageTargetSlice23A01_length]

end SmallCusp
