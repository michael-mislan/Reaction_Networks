import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation47A01

namespace SmallCusp

def sourceCoverageTargetSlice47A0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice47A00 ++
  sourceCoverageTargetSlice47A01

theorem sourceCoverageTargetSlice47A0_targetConsistent :
    sourceCoverageTargetSlice47A0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice47A0,
    sourceCoverageTargetSlice47A00_targetConsistent,
    sourceCoverageTargetSlice47A01_targetConsistent]

theorem sourceCoverageTargetSlice47A0_length : sourceCoverageTargetSlice47A0.length = 125 := by
  simp [sourceCoverageTargetSlice47A0,
    sourceCoverageTargetSlice47A00_length,
    sourceCoverageTargetSlice47A01_length]

end SmallCusp
