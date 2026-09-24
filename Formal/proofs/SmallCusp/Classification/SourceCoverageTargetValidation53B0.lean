import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B00
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53B01

namespace SmallCusp

def sourceCoverageTargetSlice53B0 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53B00 ++
  sourceCoverageTargetSlice53B01

theorem sourceCoverageTargetSlice53B0_targetConsistent :
    sourceCoverageTargetSlice53B0.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53B0,
    sourceCoverageTargetSlice53B00_targetConsistent,
    sourceCoverageTargetSlice53B01_targetConsistent]

theorem sourceCoverageTargetSlice53B0_length : sourceCoverageTargetSlice53B0.length = 125 := by
  simp [sourceCoverageTargetSlice53B0,
    sourceCoverageTargetSlice53B00_length,
    sourceCoverageTargetSlice53B01_length]

end SmallCusp
