import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation35B01

namespace SmallCusp

def sourceCoverageTargetSlice35B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice35B00 ++
  sourceCoverageTargetSlice35B01

theorem sourceCoverageTargetSlice35B0_targetConsistent :
    sourceCoverageTargetSlice35B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice35B0,
    sourceCoverageTargetSlice35B00_targetConsistent,
    sourceCoverageTargetSlice35B01_targetConsistent]

theorem sourceCoverageTargetSlice35B0_length : sourceCoverageTargetSlice35B0.length = 125 := by
  simp [sourceCoverageTargetSlice35B0,
    sourceCoverageTargetSlice35B00_length,
    sourceCoverageTargetSlice35B01_length]

end SmallCusp
