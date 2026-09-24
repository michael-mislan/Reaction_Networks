import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation59B01

namespace SmallCusp

def sourceCoverageTargetSlice59B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice59B00 ++
  sourceCoverageTargetSlice59B01

theorem sourceCoverageTargetSlice59B0_targetConsistent :
    sourceCoverageTargetSlice59B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice59B0,
    sourceCoverageTargetSlice59B00_targetConsistent,
    sourceCoverageTargetSlice59B01_targetConsistent]

theorem sourceCoverageTargetSlice59B0_length : sourceCoverageTargetSlice59B0.length = 125 := by
  simp [sourceCoverageTargetSlice59B0,
    sourceCoverageTargetSlice59B00_length,
    sourceCoverageTargetSlice59B01_length]

end SmallCusp
