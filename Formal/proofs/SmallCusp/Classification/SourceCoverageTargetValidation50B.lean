import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50B1

namespace SmallCusp

def sourceCoverageTargetSlice50B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50B0 ++
  sourceCoverageTargetSlice50B1

theorem sourceCoverageTargetSlice50B_targetConsistent :
    sourceCoverageTargetSlice50B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50B,
    sourceCoverageTargetSlice50B0_targetConsistent,
    sourceCoverageTargetSlice50B1_targetConsistent]

theorem sourceCoverageTargetSlice50B_length : sourceCoverageTargetSlice50B.length = 250 := by
  simp [sourceCoverageTargetSlice50B,
    sourceCoverageTargetSlice50B0_length,
    sourceCoverageTargetSlice50B1_length]

end SmallCusp
