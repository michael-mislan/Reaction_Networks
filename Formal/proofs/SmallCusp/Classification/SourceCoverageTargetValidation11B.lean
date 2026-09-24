import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation11B1

namespace SmallCusp

def sourceCoverageTargetSlice11B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice11B0 ++
  sourceCoverageTargetSlice11B1

theorem sourceCoverageTargetSlice11B_targetConsistent :
    sourceCoverageTargetSlice11B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice11B,
    sourceCoverageTargetSlice11B0_targetConsistent,
    sourceCoverageTargetSlice11B1_targetConsistent]

theorem sourceCoverageTargetSlice11B_length : sourceCoverageTargetSlice11B.length = 250 := by
  simp [sourceCoverageTargetSlice11B,
    sourceCoverageTargetSlice11B0_length,
    sourceCoverageTargetSlice11B1_length]

end SmallCusp
