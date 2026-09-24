import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A11

namespace SmallCusp

def sourceCoverageTargetSlice54A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54A10 ++
  sourceCoverageTargetSlice54A11

theorem sourceCoverageTargetSlice54A1_targetConsistent :
    sourceCoverageTargetSlice54A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54A1,
    sourceCoverageTargetSlice54A10_targetConsistent,
    sourceCoverageTargetSlice54A11_targetConsistent]

theorem sourceCoverageTargetSlice54A1_length : sourceCoverageTargetSlice54A1.length = 125 := by
  simp [sourceCoverageTargetSlice54A1,
    sourceCoverageTargetSlice54A10_length,
    sourceCoverageTargetSlice54A11_length]

end SmallCusp
