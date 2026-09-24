import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54B01

namespace SmallCusp

def sourceCoverageTargetSlice54B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54B00 ++
  sourceCoverageTargetSlice54B01

theorem sourceCoverageTargetSlice54B0_targetConsistent :
    sourceCoverageTargetSlice54B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54B0,
    sourceCoverageTargetSlice54B00_targetConsistent,
    sourceCoverageTargetSlice54B01_targetConsistent]

theorem sourceCoverageTargetSlice54B0_length : sourceCoverageTargetSlice54B0.length = 125 := by
  simp [sourceCoverageTargetSlice54B0,
    sourceCoverageTargetSlice54B00_length,
    sourceCoverageTargetSlice54B01_length]

end SmallCusp
