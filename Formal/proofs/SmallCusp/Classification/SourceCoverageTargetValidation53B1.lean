import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B11

namespace SmallCusp

def sourceCoverageTargetSlice53B1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53B10 ++
  sourceCoverageTargetSlice53B11

theorem sourceCoverageTargetSlice53B1_targetConsistent :
    sourceCoverageTargetSlice53B1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53B1,
    sourceCoverageTargetSlice53B10_targetConsistent,
    sourceCoverageTargetSlice53B11_targetConsistent]

theorem sourceCoverageTargetSlice53B1_length : sourceCoverageTargetSlice53B1.length = 125 := by
  simp [sourceCoverageTargetSlice53B1,
    sourceCoverageTargetSlice53B10_length,
    sourceCoverageTargetSlice53B11_length]

end SmallCusp
