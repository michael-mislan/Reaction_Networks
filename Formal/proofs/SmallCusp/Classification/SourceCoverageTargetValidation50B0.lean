import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B01

namespace SmallCusp

def sourceCoverageTargetSlice50B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50B00 ++
  sourceCoverageTargetSlice50B01

theorem sourceCoverageTargetSlice50B0_targetConsistent :
    sourceCoverageTargetSlice50B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50B0,
    sourceCoverageTargetSlice50B00_targetConsistent,
    sourceCoverageTargetSlice50B01_targetConsistent]

theorem sourceCoverageTargetSlice50B0_length : sourceCoverageTargetSlice50B0.length = 125 := by
  simp [sourceCoverageTargetSlice50B0,
    sourceCoverageTargetSlice50B00_length,
    sourceCoverageTargetSlice50B01_length]

end SmallCusp
