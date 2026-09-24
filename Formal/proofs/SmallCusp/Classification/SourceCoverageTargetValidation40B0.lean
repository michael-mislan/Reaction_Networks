import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B01

namespace SmallCusp

def sourceCoverageTargetSlice40B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40B00 ++
  sourceCoverageTargetSlice40B01

theorem sourceCoverageTargetSlice40B0_targetConsistent :
    sourceCoverageTargetSlice40B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40B0,
    sourceCoverageTargetSlice40B00_targetConsistent,
    sourceCoverageTargetSlice40B01_targetConsistent]

theorem sourceCoverageTargetSlice40B0_length : sourceCoverageTargetSlice40B0.length = 125 := by
  simp [sourceCoverageTargetSlice40B0,
    sourceCoverageTargetSlice40B00_length,
    sourceCoverageTargetSlice40B01_length]

end SmallCusp
