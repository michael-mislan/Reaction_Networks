import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation22A01

namespace SmallCusp

def sourceCoverageTargetSlice22A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice22A00 ++
  sourceCoverageTargetSlice22A01

theorem sourceCoverageTargetSlice22A0_targetConsistent :
    sourceCoverageTargetSlice22A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice22A0,
    sourceCoverageTargetSlice22A00_targetConsistent,
    sourceCoverageTargetSlice22A01_targetConsistent]

theorem sourceCoverageTargetSlice22A0_length : sourceCoverageTargetSlice22A0.length = 125 := by
  simp [sourceCoverageTargetSlice22A0,
    sourceCoverageTargetSlice22A00_length,
    sourceCoverageTargetSlice22A01_length]

end SmallCusp
