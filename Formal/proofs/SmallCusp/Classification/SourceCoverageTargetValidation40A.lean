import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40A1

namespace SmallCusp

def sourceCoverageTargetSlice40A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40A0 ++
  sourceCoverageTargetSlice40A1

theorem sourceCoverageTargetSlice40A_targetConsistent :
    sourceCoverageTargetSlice40A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40A,
    sourceCoverageTargetSlice40A0_targetConsistent,
    sourceCoverageTargetSlice40A1_targetConsistent]

theorem sourceCoverageTargetSlice40A_length : sourceCoverageTargetSlice40A.length = 250 := by
  simp [sourceCoverageTargetSlice40A,
    sourceCoverageTargetSlice40A0_length,
    sourceCoverageTargetSlice40A1_length]

end SmallCusp
