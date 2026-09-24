import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation46A01

namespace SmallCusp

def sourceCoverageTargetSlice46A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice46A00 ++
  sourceCoverageTargetSlice46A01

theorem sourceCoverageTargetSlice46A0_targetConsistent :
    sourceCoverageTargetSlice46A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice46A0,
    sourceCoverageTargetSlice46A00_targetConsistent,
    sourceCoverageTargetSlice46A01_targetConsistent]

theorem sourceCoverageTargetSlice46A0_length : sourceCoverageTargetSlice46A0.length = 125 := by
  simp [sourceCoverageTargetSlice46A0,
    sourceCoverageTargetSlice46A00_length,
    sourceCoverageTargetSlice46A01_length]

end SmallCusp
