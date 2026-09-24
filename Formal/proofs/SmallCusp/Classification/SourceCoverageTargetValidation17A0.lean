import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation17A01

namespace SmallCusp

def sourceCoverageTargetSlice17A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice17A00 ++
  sourceCoverageTargetSlice17A01

theorem sourceCoverageTargetSlice17A0_targetConsistent :
    sourceCoverageTargetSlice17A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice17A0,
    sourceCoverageTargetSlice17A00_targetConsistent,
    sourceCoverageTargetSlice17A01_targetConsistent]

theorem sourceCoverageTargetSlice17A0_length : sourceCoverageTargetSlice17A0.length = 125 := by
  simp [sourceCoverageTargetSlice17A0,
    sourceCoverageTargetSlice17A00_length,
    sourceCoverageTargetSlice17A01_length]

end SmallCusp
