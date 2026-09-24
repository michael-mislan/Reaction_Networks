import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B1

namespace SmallCusp

def sourceCoverageTargetSlice53B : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53B0 ++
  sourceCoverageTargetSlice53B1

theorem sourceCoverageTargetSlice53B_targetConsistent :
    sourceCoverageTargetSlice53B.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53B,
    sourceCoverageTargetSlice53B0_targetConsistent,
    sourceCoverageTargetSlice53B1_targetConsistent]

theorem sourceCoverageTargetSlice53B_length : sourceCoverageTargetSlice53B.length = 250 := by
  simp [sourceCoverageTargetSlice53B,
    sourceCoverageTargetSlice53B0_length,
    sourceCoverageTargetSlice53B1_length]

end SmallCusp
