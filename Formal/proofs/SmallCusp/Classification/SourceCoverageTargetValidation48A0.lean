import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation48A01

namespace SmallCusp

def sourceCoverageTargetSlice48A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice48A00 ++
  sourceCoverageTargetSlice48A01

theorem sourceCoverageTargetSlice48A0_targetConsistent :
    sourceCoverageTargetSlice48A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice48A0,
    sourceCoverageTargetSlice48A00_targetConsistent,
    sourceCoverageTargetSlice48A01_targetConsistent]

theorem sourceCoverageTargetSlice48A0_length : sourceCoverageTargetSlice48A0.length = 125 := by
  simp [sourceCoverageTargetSlice48A0,
    sourceCoverageTargetSlice48A00_length,
    sourceCoverageTargetSlice48A01_length]

end SmallCusp
