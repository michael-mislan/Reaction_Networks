import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59A01

namespace SmallCusp

def sourceCoverageTargetSlice59A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59A00 ++
  sourceCoverageTargetSlice59A01

theorem sourceCoverageTargetSlice59A0_targetConsistent :
    sourceCoverageTargetSlice59A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59A0,
    sourceCoverageTargetSlice59A00_targetConsistent,
    sourceCoverageTargetSlice59A01_targetConsistent]

theorem sourceCoverageTargetSlice59A0_length : sourceCoverageTargetSlice59A0.length = 125 := by
  simp [sourceCoverageTargetSlice59A0,
    sourceCoverageTargetSlice59A00_length,
    sourceCoverageTargetSlice59A01_length]

end SmallCusp
