import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation45B01

namespace SmallCusp

def sourceCoverageTargetSlice45B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice45B00 ++
  sourceCoverageTargetSlice45B01

theorem sourceCoverageTargetSlice45B0_targetConsistent :
    sourceCoverageTargetSlice45B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice45B0,
    sourceCoverageTargetSlice45B00_targetConsistent,
    sourceCoverageTargetSlice45B01_targetConsistent]

theorem sourceCoverageTargetSlice45B0_length : sourceCoverageTargetSlice45B0.length = 125 := by
  simp [sourceCoverageTargetSlice45B0,
    sourceCoverageTargetSlice45B00_length,
    sourceCoverageTargetSlice45B01_length]

end SmallCusp
