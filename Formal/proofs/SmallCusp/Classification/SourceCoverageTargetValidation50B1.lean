import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B11

namespace SmallCusp

def sourceCoverageTargetSlice50B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50B10 ++
  sourceCoverageTargetSlice50B11

theorem sourceCoverageTargetSlice50B1_targetConsistent :
    sourceCoverageTargetSlice50B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50B1,
    sourceCoverageTargetSlice50B10_targetConsistent,
    sourceCoverageTargetSlice50B11_targetConsistent]

theorem sourceCoverageTargetSlice50B1_length : sourceCoverageTargetSlice50B1.length = 125 := by
  simp [sourceCoverageTargetSlice50B1,
    sourceCoverageTargetSlice50B10_length,
    sourceCoverageTargetSlice50B11_length]

end SmallCusp
