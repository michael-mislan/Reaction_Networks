import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation24B01

namespace SmallCusp

def sourceCoverageTargetSlice24B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice24B00 ++
  sourceCoverageTargetSlice24B01

theorem sourceCoverageTargetSlice24B0_targetConsistent :
    sourceCoverageTargetSlice24B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice24B0,
    sourceCoverageTargetSlice24B00_targetConsistent,
    sourceCoverageTargetSlice24B01_targetConsistent]

theorem sourceCoverageTargetSlice24B0_length : sourceCoverageTargetSlice24B0.length = 125 := by
  simp [sourceCoverageTargetSlice24B0,
    sourceCoverageTargetSlice24B00_length,
    sourceCoverageTargetSlice24B01_length]

end SmallCusp
