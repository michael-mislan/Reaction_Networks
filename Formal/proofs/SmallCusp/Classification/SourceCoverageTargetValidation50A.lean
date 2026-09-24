import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A1

namespace SmallCusp

def sourceCoverageTargetSlice50A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50A0 ++
  sourceCoverageTargetSlice50A1

theorem sourceCoverageTargetSlice50A_targetConsistent :
    sourceCoverageTargetSlice50A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50A,
    sourceCoverageTargetSlice50A0_targetConsistent,
    sourceCoverageTargetSlice50A1_targetConsistent]

theorem sourceCoverageTargetSlice50A_length : sourceCoverageTargetSlice50A.length = 250 := by
  simp [sourceCoverageTargetSlice50A,
    sourceCoverageTargetSlice50A0_length,
    sourceCoverageTargetSlice50A1_length]

end SmallCusp
