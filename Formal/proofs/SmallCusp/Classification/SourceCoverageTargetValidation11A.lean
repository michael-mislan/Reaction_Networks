import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11A1

namespace SmallCusp

def sourceCoverageTargetSlice11A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice11A0 ++
  sourceCoverageTargetSlice11A1

theorem sourceCoverageTargetSlice11A_targetConsistent :
    sourceCoverageTargetSlice11A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice11A,
    sourceCoverageTargetSlice11A0_targetConsistent,
    sourceCoverageTargetSlice11A1_targetConsistent]

theorem sourceCoverageTargetSlice11A_length : sourceCoverageTargetSlice11A.length = 250 := by
  simp [sourceCoverageTargetSlice11A,
    sourceCoverageTargetSlice11A0_length,
    sourceCoverageTargetSlice11A1_length]

end SmallCusp
