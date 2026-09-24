import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A10
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A11

namespace SmallCusp

def sourceCoverageTargetSlice53A1 : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53A10 ++
  sourceCoverageTargetSlice53A11

theorem sourceCoverageTargetSlice53A1_targetConsistent :
    sourceCoverageTargetSlice53A1.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53A1,
    sourceCoverageTargetSlice53A10_targetConsistent,
    sourceCoverageTargetSlice53A11_targetConsistent]

theorem sourceCoverageTargetSlice53A1_length : sourceCoverageTargetSlice53A1.length = 125 := by
  simp [sourceCoverageTargetSlice53A1,
    sourceCoverageTargetSlice53A10_length,
    sourceCoverageTargetSlice53A11_length]

end SmallCusp
