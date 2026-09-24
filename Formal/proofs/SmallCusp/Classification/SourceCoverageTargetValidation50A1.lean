import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation50A11

namespace SmallCusp

def sourceCoverageTargetSlice50A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice50A10 ++
  sourceCoverageTargetSlice50A11

theorem sourceCoverageTargetSlice50A1_targetConsistent :
    sourceCoverageTargetSlice50A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice50A1,
    sourceCoverageTargetSlice50A10_targetConsistent,
    sourceCoverageTargetSlice50A11_targetConsistent]

theorem sourceCoverageTargetSlice50A1_length : sourceCoverageTargetSlice50A1.length = 125 := by
  simp [sourceCoverageTargetSlice50A1,
    sourceCoverageTargetSlice50A10_length,
    sourceCoverageTargetSlice50A11_length]

end SmallCusp
