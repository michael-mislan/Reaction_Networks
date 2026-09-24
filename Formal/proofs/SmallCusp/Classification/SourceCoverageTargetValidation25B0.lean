import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation25B01

namespace SmallCusp

def sourceCoverageTargetSlice25B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice25B00 ++
  sourceCoverageTargetSlice25B01

theorem sourceCoverageTargetSlice25B0_targetConsistent :
    sourceCoverageTargetSlice25B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice25B0,
    sourceCoverageTargetSlice25B00_targetConsistent,
    sourceCoverageTargetSlice25B01_targetConsistent]

theorem sourceCoverageTargetSlice25B0_length : sourceCoverageTargetSlice25B0.length = 125 := by
  simp [sourceCoverageTargetSlice25B0,
    sourceCoverageTargetSlice25B00_length,
    sourceCoverageTargetSlice25B01_length]

end SmallCusp
