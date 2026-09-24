import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation54A1

namespace SmallCusp

def sourceCoverageTargetSlice54A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice54A0 ++
  sourceCoverageTargetSlice54A1

theorem sourceCoverageTargetSlice54A_targetConsistent :
    sourceCoverageTargetSlice54A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice54A,
    sourceCoverageTargetSlice54A0_targetConsistent,
    sourceCoverageTargetSlice54A1_targetConsistent]

theorem sourceCoverageTargetSlice54A_length : sourceCoverageTargetSlice54A.length = 250 := by
  simp [sourceCoverageTargetSlice54A,
    sourceCoverageTargetSlice54A0_length,
    sourceCoverageTargetSlice54A1_length]

end SmallCusp
