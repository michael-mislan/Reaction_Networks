import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation40B1

namespace SmallCusp

def sourceCoverageTargetSlice40B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice40B0 ++
  sourceCoverageTargetSlice40B1

theorem sourceCoverageTargetSlice40B_targetConsistent :
    sourceCoverageTargetSlice40B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice40B,
    sourceCoverageTargetSlice40B0_targetConsistent,
    sourceCoverageTargetSlice40B1_targetConsistent]

theorem sourceCoverageTargetSlice40B_length : sourceCoverageTargetSlice40B.length = 250 := by
  simp [sourceCoverageTargetSlice40B,
    sourceCoverageTargetSlice40B0_length,
    sourceCoverageTargetSlice40B1_length]

end SmallCusp
