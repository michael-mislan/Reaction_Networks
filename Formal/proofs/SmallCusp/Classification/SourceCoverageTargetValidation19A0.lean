import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation19A01

namespace SmallCusp

def sourceCoverageTargetSlice19A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice19A00 ++
  sourceCoverageTargetSlice19A01

theorem sourceCoverageTargetSlice19A0_targetConsistent :
    sourceCoverageTargetSlice19A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice19A0,
    sourceCoverageTargetSlice19A00_targetConsistent,
    sourceCoverageTargetSlice19A01_targetConsistent]

theorem sourceCoverageTargetSlice19A0_length : sourceCoverageTargetSlice19A0.length = 125 := by
  simp [sourceCoverageTargetSlice19A0,
    sourceCoverageTargetSlice19A00_length,
    sourceCoverageTargetSlice19A01_length]

end SmallCusp
