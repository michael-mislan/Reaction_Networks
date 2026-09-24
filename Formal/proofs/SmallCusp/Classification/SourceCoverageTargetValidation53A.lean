import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A0
import proofs.SmallCusp.Classification.SourceCoverageTargetValidation53A1

namespace SmallCusp

def sourceCoverageTargetSlice53A : List SourceCoverageRecord :=
  sourceCoverageTargetSlice53A0 ++
  sourceCoverageTargetSlice53A1

theorem sourceCoverageTargetSlice53A_targetConsistent :
    sourceCoverageTargetSlice53A.all (fun R => decide R.TargetConsistent) = true := by
  simp [sourceCoverageTargetSlice53A,
    sourceCoverageTargetSlice53A0_targetConsistent,
    sourceCoverageTargetSlice53A1_targetConsistent]

theorem sourceCoverageTargetSlice53A_length : sourceCoverageTargetSlice53A.length = 250 := by
  simp [sourceCoverageTargetSlice53A,
    sourceCoverageTargetSlice53A0_length,
    sourceCoverageTargetSlice53A1_length]

end SmallCusp
